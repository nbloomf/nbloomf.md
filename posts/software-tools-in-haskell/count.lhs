---
title: Software Tools in Haskell: count
subtitle: count lines or chars on stdin
author: nbloomf
date: 2016-02-11
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-count: count lines or chars on stdin
> module Main where
> 
> import System.Exit (exitSuccess)
> import System.Environment (getArgs)
> import Control.Arrow ((>>>))
> import Data.List (unfoldr)
> import Data.Foldable (foldl')

*Software Tools* includes two programs -- ``charcount`` and ``linecount`` -- which count chars and lines on ``stdin``, respectively. Because these functions are so similar, and we anticipate that counting lines will be more useful in practice than counting characters, we'll combine these into one program and trigger character counting with an optional command line argument. ``count`` is a filter, taking either char or line text and producing a line.


Counting Chars
--------------

We want ``count --char`` to count the characters on stdin until EOF is reached. Almost right off the bat we have a problem: with Unicode it is not obvious what a "character" is. For simplicity's sake I will split this problem in two: ``count --char``, which ignores any issues with unicode normalization like combining diacritics, and ``glyphcount``, which takes these issues into account. So for instance O̰ (capital O, with combining tilde below) counts as two characters but one glyph. Character encodings were much simpler and less useful when *Software Tools* was written. 🙂

Let's write a generic list-length counter:

> count :: (Num t) => [a] -> t
> count = foldl' inc 0
>   where inc n _ = n+1

We use ``foldl'`` to force strictness and avoid a memory leak. The ``foldl`` function is lazy by default, meaning that it would generate a stack of unevaluated additions to be carried out only once EOF is reached.


Counting Lines
--------------

By default, ``count`` counts lines on ``stdin`` until EOF is reached. Now while the definition of "character" is reasonably clear (unicode notwithstanding), we have to think more carefully about what a "line" is.

By custom on unix systems the "newline" character, denoted ``\n``, signals the end of a line. To a first approximation we can march down the sequence of characters on ``stdin`` and count the ``\n``s. But is every line necessarily terminated by a newline? What if there are *no* newlines? It seems wrong to say that a sequence of characters containing no newlines consists of zero lines. More generally, if a sequence of characters does not terminate in a newline, then the characters between the last ``\n`` and EOF should comprise a line. For example, the sequence of characters

    foo\nbar\nbaz

should have three lines, not two. On the other hand, if there are *no* characters on stdin, then there are no lines. These edge cases are nicely handled by defining a *line* to be a maximal subsequence of a nonempty sequence of characters which does not include a newline. More concretely,

* the empty sequence consists of zero lines, and
* given a nonempty sequence of characters in which ``\n`` appears $k$ times, the number of lines in the sequence is $k$ if the last character is ``\n`` and is $k+1$ otherwise.

This logic is captured by the ``getLines`` function, which splits a string into lines at ``\n`` (taking care of any ``\n``s at the end as necessary).

> getLines :: String -> [String]
> getLines = unfoldr firstLine
>   where
>     firstLine :: String -> Maybe (String, String)
>     firstLine xs = case break (== '\n') xs of
>       ("","")   -> Nothing
>       (as,"")   -> Just (as,"")
>       (as,b:bs) -> Just (as,bs)


The Program
-----------

Our main program is a little more complicated than Kernighan and Plauger's because we've chosen to deal with command line arguments.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   case args of
>     ["--char"] -> do
>       charFilter (show . count)
>       putNewLine
>     otherwise -> do
>       charFilter (getLines >>> count >>> show)
>       putNewLine
> 
>   exitSuccess

``putNewLine`` is a semantic synonym for ``putStrLn ""``.

> -- print a line break
> putNewLine :: IO ()
> putNewLine = putStrLn ""
> 
> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs

Note also that we've demonstrated the ``>>>`` operator from ``Control.Arrow`` in contrast with composition. This is a standard library operator which (used here) is simply reversed function composition; it allows us to read chains of functions as if data flows from left to right, following the arrows.
