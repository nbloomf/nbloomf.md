---
title: Software Tools in Haskell: glyphcount, wordcount, sentcount
author: nbloomf
date: 2016-02-22
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.


<a name="glyphcount" />

## ``glyphcount``: count glyphs on stdin

When we ported [``charcount``](/posts/2016-02-11-software-tools-in-haskell-copy-charcount-linecount.html#charcount), we saw that there is a serious ambiguity in the meaning of "character" in Unicode. On one hand Unicode defines a list of character code points, but on the other hand sequences of code points do not necessarily correspond to symbols on the screen in the way ASCII characters do. In fact there is a [Unicode Technical Report](http://www.unicode.org/reports/tr17/#CharactersVsGlyphs) which addresses this ambiguity; unfortunately the conclusion there is that

> The correspondence between glyphs and characters is generally not one-to-one, and cannot be predicted from the text alone. <cite>Unicode Technical Report #17</cite>

Given this difficulty, we will make a simplifying assumption. **A "glyph" is a non-combining character followed by zero or more combining characters.** Fortunately there is a standard library function, ``isMark``, which detects which characters are combining diacritics. The ``getGlyphs`` function splits a string into a list of glyphs.


```haskell
getGlyphs :: String -> [String]
getGlyphs = unfoldr firstGlyph
  where
    firstGlyph :: String -> Maybe (String, String)
    firstGlyph "" = Nothing
    firstGlyph (x:xs) = if isMark x
      then Just $ break (not . isMark) (x:xs)
      else do
        let (as,bs) = break (not . isMark) xs
        Just (x:as, bs)
```


Now the main function is much like ``linecount``.


```haskell
module Main where

import Control.Arrow ((>>>))
import SoftwareTools.FunctionLibrary (count, getGlyphs)

main :: IO ()
main = getContents >>=
  (getGlyphs >>> count >>> show >>> putStrLn)
```



<a name="wordcount" />

## ``wordcount``: count words on stdin

This program takes an expansive view of what a "word" is: maximal substrings not containing any whitespace characters (space, ``\n``, ``\t``, ``\r``, ``\v``, or any other unicode character which the standard ``isSpace`` function detects).


```haskell
getWords :: String -> [String]
getWords = unfoldr firstWord
  where
    firstWord :: String -> Maybe (String, String)
    firstWord xs = case dropWhile isSpace xs of
      "" -> Nothing
      ys -> Just $ break isSpace ys
```


For this function we used ``getContents`` and reused ``count``. The ``getWords`` function takes a string and splits it into a list of words, with delimiting spaces removed. There is a standard library function in ``Data.List``, called (appropriately enough) ``words``, that does this. But the whole point of this exercise is reinventing wheels, and besides ``wc`` does all this better anyway. :)


```haskell
module Main where

import Control.Arrow ((>>>))
import SoftwareTools.FunctionLibrary (count, getWords)

main :: IO ()
main = getContents >>=
  (getWords >>> count >>> show >>> putStrLn)
```


Both ``getWords`` and ``count`` use standard library recursion operators, ``unfoldr`` and ``foldl'``. Recursion is how functional languages handle iterated computation (a.k.a. "loops"). But much like structured programming replaced arbitrary GOTOs with a small number of control-flow statements, in functional languages we can get a lot of mileage out of a small number of recursion patterns.



<a name="sentcount" />

## ``sentcount``: count sentences on stdin

This program is an exercise in *Software Tools*, rather than a main example.

If we don't think about it very long, counting sentences seems simple enough; much like we did when counting words, simply decide what strings of characters mark the boundaries between "sentences" and "non-sentences" and keep track of the number of state changes. Sentences are usually terminated by periods, with some exclamation points and question marks: done.

"But wait," you ask, "what about quoted sentences?" (I hadn't thought of that. Or parenthetical sentences, for that matter. (Much less nested parenthetical sentences.)) There's also the issue of short parenthetical asides at the end of a sentence (like this one). Even periods cannot be relied upon to denote sentence ends, since they serve double (triple?) duty as ellipses and as parts of words as in abbreviations. What about the beginnings of sentences? mRNA is a proper noun whose first letter should not be capitalized, which breaks the usual rule that sentences start with a capital letter. Interjections, like POW! and BZZT!, look like sentence enders but may not be. And of course some forms like poetry or mathematical notation throw some rules out the window. (Is "$ax^2 + bx + c = 0$" a sentence? It sounds like one if read aloud.) Upon further reflection, it appears that English sentences are extremely complicated.

I will go out on a limb and say that the full problem of deciding whether a given list of characters is a (standard English) sentence is probably AI-complete, in that any algorithm which could do this with 100% accuracy (if that even makes sense) would need to "understand" the *meaning* of the text. At the very least, approaching 100% accuracy likely requires a large dictionary of things like proper nouns and abbreviations, to handle special cases.

The point of all this waffling is that **this problem is extremely hard** and therefore **we cannot find a complete solution**. The best we can hope for is an approximate solution that is not terribly wrong most of the time. To that end, our sentence-counting program will make some simplifying assumptions.

1. We only consider standard English prose. Other languages, or other forms of text, are assumed to give meaningless sentence counts.
2. In standard English prose, the end of a sentence is almost always signified by the appearance of one of three punctuation marks: period, exclamation point, or question mark. There may be other punctuation involved, but one of these three should be present.
3. We assume that every *sentence* boundary is also a *word* boundary.

Our basic strategy is this: first split our text into words, using the ``getWords`` function from ``wordcount``. Then use some heuristics to decide which word boundaries are also sentence boundaries. These heuristics will be allowed to look only at the words immediately on either side of a word boundary. (This is probably too restrictive in general, but reasonable.) For instance, a string like

    harpoons. After

consists of two words (by our reckoning), and we will say it is likely to be a sentence boundary. Other examples are similar.

    ever." She

    casserole! (Gumbo

Again, any small set of heuristics is probably going to have both false positives and false negatives. But we're not aiming for perfection here, just reasonable first approximations. We start with some helper functions: ``break2`` and ``getSentences``.


```haskell
break2 :: (a -> a -> Bool) -> [a] -> ([a],[a])
break2 p xs = foo [] xs
  where
    foo acc []  = (reverse acc, [])
    foo acc [y] = (reverse (y:acc), [])
    foo acc (y1:y2:ys) = if p y1 y2
      then (reverse (y1:acc), y2:ys)
      else foo (y1:acc) (y2:ys)

getSentences :: String -> [String]
getSentences = map (intercalate " ") . unfoldr firstSentence . getWords
  where
    firstSentence :: [String] -> Maybe ([String],[String])
    firstSentence [] = Nothing
    firstSentence xs = Just $ break2 isSentenceBoundary xs

    isSentenceBoundary :: String -> String -> Bool
    isSentenceBoundary xs ys
      | finalEllipsis xs && not (isSentenceStart ys) = False
      | isSentenceEnd xs && isSentenceStart ys = True
      | otherwise = False
      where
        isCapitalized ""    = False
        isCapitalized (x:_) = isUpper x

        finalEllipsis :: String -> Bool
        finalEllipsis xs = or $ map (`isSuffixOf` xs)
          ["...", "...\"", "...)"]

        isSentenceEnd :: String -> Bool
        isSentenceEnd xs = or $ map (`isSuffixOf` xs)
          [ ".", ".\"", ".'", ".)"
          , "!", "!\"", "!'", "!)"
          , "?", "?\"", "?'", "?)"
          ]

        isSentenceStart :: String -> Bool
        isSentenceStart ys = (isCapitalized ys)
          || (or $ map (`isPrefixOf` ys) ["\"", "'", "("])
```


The ``break2`` function is an extension of the standard library function ``break`` that focuses on the spaces between list elements rather than list elements themselves. (Note that ``break p === break2 (\x _ -> p x)``.) ``getSentences`` does the heavy lifting, splitting a string into sentences using heuristics. The heuristics for detecting sentence boundaries are in ``isSentenceBoundary``. This function is ugly, but reasonably easy to modify as new special cases arise.


```haskell
module Main where

import Control.Arrow ((>>>))
import SoftwareTools.FunctionLibrary (count, getSentences)

main :: IO ()
main = getContents >>=
  (getSentences >>> count >>> show >>> putStrLn)
```


We [test](https://raw.githubusercontent.com/nbloomf/st-haskell/master/test/sentcount/alice.test) this program on a particularly messy excerpt from *Alice in Wonderland*, courtesy of [Project Gutenberg](http://www.gutenberg.org). (Even counting by hand I'm not sure how many sentences this example should have!)

The main functions of ``linecount``, ``glyphcount``, ``wordcount``, and ``sentcount`` are essentially the same; each one splits the ``stdin`` into appropriate chunks and then counts.
