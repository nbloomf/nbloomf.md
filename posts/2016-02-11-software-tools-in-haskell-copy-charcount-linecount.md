---
title: Software Tools in Haskell: copy, charcount, linecount
author: nbloomf
date: 2016-02-11
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.


<a name="copy" />

## ``copy``: copy characters from stdin to stdout

Many simple tools are designed to act as *filters*: programs which take a stream of data, manipulate it in some way, and send it along. The ``copy`` program is the simplest possible example of a filter -- the identity filter. This is even simpler than ``cat``, which at least catenates files.

This program copies characters from stdin to stdout until EOF is encountered, whereupon it exits. Any other error causes the program to fail. In an imperative language this pattern (read a character, write a character, repeat) would be written with a loop. In Haskell we instead use recursion.


```haskell
module Main where

import System.IO (getChar, putChar)
import SoftwareTools.FunctionLibrary (catchEOF)

main :: IO ()
main = catchEOF getChar >>= putChar >> main
```


IO actions can throw IO errors, which (unlike other error handling strategies in Haskell) can be silently, and thus accidentally, ignored. These errors are caught
using ``catchIOError``, which takes an action to be attempted and an error handler. Here, the IO action ``getChar`` may fail. In fact it will fail once the recursion reaches the end of the input. We will detect IO errors, and exit accordingly, using the ``catchEOF`` helper function. We'll stash this in the library for future use.


```haskell
catchEOF :: IO a -> IO a
catchEOF x = catchIOError x handler
  where
    handler err
      | isEOFError err = exitSuccess
      | otherwise      = exitFailure
```


<a name="charcount" />

## ``charcount``: count characters on stdin

The ``charcount`` program counts the characters on stdin until EOF is reached. Almost right off the bat we have a problem: with Unicode it is not obvious what a "character" is. For simplicity's sake I will split this program in two: ``charcount``, which ignores any issues with unicode normalization, like combining diacritics, and ``glyphcount``, which takes these issues into account. So for instance O̰ (capital O, with combining tilde below) counts as two characters but one glyph. Character encodings were much simpler and less useful when *Software Tools* was written. 🙂


```haskell
module Main where

import SoftwareTools.FunctionLibrary (count)

main :: IO ()
main = getContents
  >>= (putStrLn . show . count)
```


The ``getContents`` function reads stdin lazily, meaning that characters are only read as needed, and also handles EOF for us.


```haskell
count :: [a] -> Integer
count = foldl' inc 0
  where inc n _ = n+1
```


The ``count`` function is a helper that (you guessed it!) counts the items in a list. We use ``foldl'`` to force strictness and avoid a memory leak. The ``foldl`` function is lazy by default, meaning that it would generate a stack of unevaluated additions to be carried out only once EOF is reached.



<a name="linecount" />

## ``linecount``: count lines on stdin

The ``linecount`` program counts lines on stdin until EOF is reached. Now while the definition of "character" is reasonably clear (unicode notwithstanding), we have to think more carefully about what a "line" is.

By custom on unix systems the "newline" character, denoted ``\n``, signals the end of a line. To a first approximation we can march down the sequence of characters on stdin and count the ``\n``s. But is every line necessarily terminated by a newline? What if there are *no* newlines? It seems wrong to say that a sequence of characters containing no newlines consists of zero lines. More generally, if a sequence of characters does not terminate in a newline, then the characters between the last ``\n`` and EOF should comprise a line. For example, the sequence of characters

    foo\nbar\nbaz

should have three lines, not two. On the other hand, if there are *no* characters on stdin, then there are no lines. So our logic for counting lines is as follows.

* The empty sequence consists of zero lines.
* Given a nonempty sequence of characters, let $k$ denote the number of times ``\n`` appears. Then the number of lines in this sequence is $k$ if the last character is ``\n``, and is $k+1$ otherwise.

This logic is captured by the ``getLines`` function, which splits a string into lines at ``\n`` (taking care of any ``\n``s at the end as necessary). We reuse the ``count`` function from ``charcount``.


```haskell
getLines :: String -> [String]
getLines = unfoldr firstLine
  where
    firstLine :: String -> Maybe (String, String)
    firstLine xs = case break (== '\n') xs of
      ("","")   -> Nothing
      (as,"")   -> Just (as,"")
      (as,b:bs) -> Just (as,bs)
```


One more change from ``charcount`` is that we've used the ``>>>`` operator from ``Control.Arrow``. This is a standard library operator which (used here) is simply reversed function composition; it allows us to read the definition of ``main`` as if data flows from left to right, following the arrows. Compare this notation to the ``main`` function in ``charcount``, where we used ordinary function composition.


```haskell
module Main where

import Control.Arrow ((>>>))
import SoftwareTools.FunctionLibrary (getLines, count)

main :: IO ()
main = getContents >>=
  (getLines >>> count >>> show >>> putStrLn)
```
