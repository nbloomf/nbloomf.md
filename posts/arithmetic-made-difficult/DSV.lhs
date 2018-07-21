---
title: Delimiter Separated Values
author: nbloomf
date: 2018-07-19
tags: arithmetic-made-difficult, literate-haskell
slug: dsv
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DSV
>   ( main_dsv
>   ) where
> 
> import Testing

We've been developing an algebra of lists for a while -- now let's try to do something interesting with it.

In unix-like environments files are lists of bytes. Many of the standard unix utilities are designed to manipulate files as lists of bytes. And text-based 'formats' like YAML and JSON are essentially encodings of some abstract structures as lists of characters. To what extent can text based tools and formats be reasoned about using the algebra of lists?

In this post we'll explore this idea a bit for one of the oldest and simplest textual "formats": [delimiter separated values](https://en.wikipedia.org/wiki/Delimiter-separated_values). DSV is just barely a format at all. Simple as it is, DSV even has a registered [MIME type](https://www.iana.org/assignments/media-types/text/tab-separated-values).

Typically a DSV file is one or more lines, called _records_, each consisting of one or more _fields_, which are separated by a _delimiter_ character, usually tab but sometimes comma, semicolon, or pipe. DSV is a simple encoding for data stored as a two-dimensional array. For example:

    field1    -->|field2    -->|field3    -->|field4
    field1    -->|field2    -->|field3    -->|field4

The 'standard' for DSV, such as it is, suggests that the first line consists of 'column labels' for the records, and that each record must have the same number of fields. But in practice this is not really enforced. Also, in the simplest implementation of DSV, the fields cannot include literal newlines or delimiter characters; this weakness is one of the reasons the more complicated CSV is used, where the fields are optionally quoted.

DSV is a kind of _encoding_: a map from some set (the things being encoded) to the set of strings over an alphabet. It's tempting to think of the encoding and the encoded thing as being the same, but they are not!

So what kind of things does DSV encode? A DSV file is literally defined as a list of records, where each record is a list of fields, and each field is a list of characters. So we can say that DSV is a "function" $$\mathsf{DSV} : \lists{\lists{\lists{U}}} \rightarrow \lists{U},$$ where $U$ is the set of unicode code points.

By casting DSV in this language, we can ask some interesting questions.

1. Does the DSV encoding really represent a function? That is, does every list of records have a unique encoding?
2. If encoding really is a function, is it surjective? This is a very practical question. If not, then there is some list of characters that cannot be decoded, so DSV files would be subject to validation. If encoding is surjective, on the other hand, then we never have to worry about "parse errors" because every list of characters is the encoding of some list of records.
3. If DSV encoding really is a function, is it injective? This is also a practical question. If not, then the encoding process is destructive -- there are distinct lists of records with the same encoding.

The IANA definition of DSV encoding is not a function from lists of lists of strings to strings, because not every such list can be encoded -- in particular, any fields including literal tabs. The usual way to get around this restriction is with an [_escaping_ mechanism](https://en.wikipedia.org/wiki/Escape_character): a special character indicating that the character after it is not to be interpreted literally. In unix this is usually the backslash, and usually a backslash _always_ escapes the character it precedes.

We can think of the escape character as letting us augment the character set at the expense of an additional tokenization step.

Say we try to fix the IANA DSV definition by introducing an escape character -- `@` -- and say that `@` followed by tab is not a field separator, but represents a literal tab. Same for newlines. Now our encoding really is a function on arbitrary records, since we can now encode any character. But we also have to decide what `@` means if it isn't followed by a tab or newline. Maybe there's a number of other escape sequences with special meanings; maybe `@` followed by a non-delimiter character represents that character; maybe an escape character that isn't part of an escape sequence is an error. Each of these choices requires making our encoding function either not surjective (if escape sequences have to be validated) or not injective (if some characters have both raw and escaped representations). Moreover, encoding is _badly_ not surjective or injective.

Another way to deal with the escape character is to decree that it is only meaningful when followed by a delimiter, and otherwise just represents itself. This might seem strange at first -- it did to me, anyway -- but it turns out this lets us recover encoding surjectivity and near-injectivity (with only one exception).

Enough motivation, let's define an encoding.

Rather than defining a full on DSV-like encoding in one go, we're going to start with an encoding for single records. With our escape convention, this will be enough to bootstrap an encoding for lists of lists of ... of lists of strings, to any depth.

(@@@)

> main_dsv :: IO ()
> main_dsv = return ()
