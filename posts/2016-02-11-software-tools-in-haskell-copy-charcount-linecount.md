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
import System.IO.Error (isEOFError, catchIOError)
import System.Exit (exitSuccess, exitFailure)

main :: IO ()
main = catchIOError getChar handler >>= putChar >> main

handler :: IOError -> IO a
handler err
  | isEOFError err = exitSuccess
  | otherwise      = exitFailure
```


IO actions can throw IO errors, which (unlike other error handling strategies in Haskell) can be silently, and thus accidentally, ignored. These errors are caught
using ``catchIOError``, which takes an action to be attempted and an error handler. Here, the IO action ``getChar`` may fail. In fact it will fail once the recursion reaches the end of the input.


<a name="charcount" />

## ``charcount``: count characters on stdin

The ``charcount`` program counts the characters on stdin until EOF is reached. 

```haskell
module Main where

import Data.Foldable (foldl')

main :: IO ()
main = getContents >>= (putStrLn . show . count)

count :: [a] -> Integer
count = foldl' inc 0
  where inc n _ = n+1
```

The ``getContents`` function reads stdin lazily, meaning that characters are only read as needed, and also handles EOF for us. Here we've written ``count`` as a ``foldl'`` to force strictness and avoid blowing out the stack. The ``foldl`` function is lazy by default, meaning that it would generate a stack of unevaluated additions to be carried out only once EOF is reached.



<a name="linecount" />

## ``linecount``: count lines on stdin

The ``linecount`` program counts lines on stdin until EOF is reached. Now while the definition of "character" is reasonably clear (unicode notwithstanding), we have to think more carefully about what a "line" is.

By custom on unix systems the "newline" character, denoted ``\n``, signals the end of a line. To a first approximation we can march down the sequence of characters on stdin and count the ``\n``s. But is every line necessarily terminated by a newline? What if there are *no* newlines? It seems wrong to say that a sequence of characters containing no newlines consists of zero lines. More generally, if a sequence of characters does not terminate in a newline, then the characters between the last ``\n`` and EOF should comprise a line. For example, the sequence of characters

    foo\nbar\nbaz

should have three lines, not two. On the other hand, if there are *no* characters on stdin, then there are no lines. So our logic for counting lines is as follows.

* The empty sequence consists of zero lines.
* Given a nonempty sequence of characters, let $k$ denote the number of times ``\n`` appears. Then the number of lines in this sequence is $k$ if the last character is ``\n``, and is $k+1$ otherwise.

This logic is captured by the ``getNewlines`` function, which extracts the ``\n``s from a sequence of characters (adding one at the end if necessary). We reuse the ``count`` function from ``charcount``.

```haskell
module Main where

import Data.Foldable (foldl')
import Control.Arrow ((>>>))

main :: IO ()
main = getContents >>=
        (getNewlines >>> count >>> show >>> putStrLn)

getNewlines :: [Char] -> [Char]
getNewlines []     = []
getNewlines [_]    = ['\n']
getNewlines (x:xs)
  | x == '\n' = '\n' : getNewlines xs
  | otherwise = getNewlines xs

count :: [a] -> Integer
count = foldl' inc 0
  where inc n _ = n+1
```

One more change from ``charcount`` is that we've used the ``>>>`` operator from ``Control.Arrow``. This is a standard library operator which (used here) is simply reversed function composition; it allows us to read the definition of ``main`` as if data flows from left to right, following the arrows. Compare this notation to the ``main`` function in ``charcount``, where we used ordinary function composition.
