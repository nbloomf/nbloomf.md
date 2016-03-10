---
title: Software Tools in Haskell: wordcount
subtitle: count words on stdin
author: nbloomf
---

This program takes an expansive view of what a "word" is: maximal substrings not containing any whitespace characters (space, ``\n``, ``\t``, ``\r``, ``\v``, or any other unicode character which the standard ``isSpace`` function detects). For instance, the following are all "words".

    atrocious  1234  --char  #$#%#$@^^^  "Horatio,

We already have a function to count items in a list. The ``getWords`` function splits a string of text into a list of words.


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
-- sth-wordcount: count words on stdin

module Main where

import System.Exit (exitSuccess)
import STH.Lib
  (charFilter, putNewLine, count, getWords)

main :: IO ()
main = do
  charFilter (show . count . getWords)
  putNewLine
  exitSuccess
```


Both ``getWords`` and ``count`` use standard library recursion operators, ``unfoldr`` and ``foldl'``. Recursion is how functional languages handle iterated computation (a.k.a. "loops"). But much like structured programming replaced arbitrary GOTOs with a small number of control-flow statements, in functional languages we can get a lot of mileage out of a small number of recursion patterns.
