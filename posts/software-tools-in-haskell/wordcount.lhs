---
title: "Software Tools in Haskell: wordcount"
subtitle: count words on stdin
date: 2016-02-12
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-wordcount: count words on stdin
> 
> module Main where
> 
> import System.Exit (exitSuccess)
> import Data.Char (isSpace)
> import Data.List (unfoldr)
> import Data.Foldable (foldl')

This program takes an expansive view of what a "word" is: maximal substrings not containing any whitespace characters (space, ``\n``, ``\t``, ``\r``, ``\v``, or any other unicode character which the standard ``isSpace`` function detects). For instance, the following are all "words".

    atrocious  1234  --char  #$#%#$@^^^  "Horatio,

We already have a function to count items in a list. The ``getWords`` function splits a string of text into a list of words.

> -- split a string into words
> getWords :: String -> [String]
> getWords = unfoldr firstWord
>   where
>     firstWord :: String -> Maybe (String, String)
>     firstWord xs = case dropWhile isSpace xs of
>       "" -> Nothing
>       ys -> Just $ break isSpace ys
> 
> -- generic length
> count :: (Num t) => [a] -> t
> count = foldl' inc 0
>   where inc n _ = n+1
>
> -- print a line break
> putNewLine :: IO ()
> putNewLine = putStrLn ""
> 
> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs

For this function we used ``getContents`` and reused ``count``. The ``getWords`` function takes a string and splits it into a list of words, with delimiting spaces removed. There is a standard library function in ``Data.List``, called (appropriately enough) ``words``, that does this. But the whole point of this exercise is reinventing wheels, and besides ``wc`` does all this better anyway. :)

> main :: IO ()
> main = do
>   charFilter (show . count . getWords)
>   putNewLine
>   exitSuccess

Both ``getWords`` and ``count`` use standard library recursion operators, ``unfoldr`` and ``foldl'``. Recursion is how functional languages handle iterated computation (a.k.a. "loops"). But much like structured programming replaced arbitrary GOTOs with a small number of control-flow statements, in functional languages we can get a lot of mileage out of a small number of recursion patterns.
