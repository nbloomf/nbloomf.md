---
title: Software Tools in Haskell: escape
subtitle: replace strange chars on stdin with escape sequences
date: 2016-02-22
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-02-22-software-tools-in-haskell-escape.lhs) into GHCi and play along. As usual, we start with some imports.

> -- sth-escape: replace non-printable, non-ascii chars on stdin with c escape sequences
> module Main where
> 
> import System.Exit (exitSuccess)
> import Data.Char (ord)
> import Data.List (unfoldr)
> import System.Environment (getArgs)

The ``escape`` program is the companion of [``unescape``](/posts/2016-02-21-software-tools-in-haskell-unescape.html); it replaces any non-printing, non-ASCII characters with C-style escape sequences using only visible ASCII. We need to be careful about exactly which characters to escape; lined text is delimited by ``\n``s, and converting these to escaped form would destroy the format. Keeping with the convention that line text is the most common, by default we leave newlines alone. The ``--char`` flag instructs ``escape`` to escape all characters.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   case args of
>     ["--char"] -> charFilter bsEsc
>     otherwise  -> lineFilter bsEsc
> 
>   exitSuccess

The work is done by ``bsEsc``:

> bsEsc :: String -> String
> bsEsc = concatMap esc
> 
> esc :: Char -> String
> esc x
>   | 32 <= k && k <= 126 = [x]
>   | k == 7    = "\\a"
>   | k == 8    = "\\b"
>   | k == 9    = "\\t"
>   | k == 10   = "\\n"
>   | k == 11   = "\\v"
>   | k == 12   = "\\f"
>   | k == 13   = "\\r"
>   | k == 27   = "\\e"
>   | k < 256   = "\\x" ++ show2Hex k
>   | k < 65536 = "\\u" ++ show4Hex k
>   | otherwise = "\\U" ++ show8Hex k
>   where
>     k = ord x
> 
>     show2Hex t = reverse $ take 2 (reverse (showHex t) ++ (repeat '0'))
>     show4Hex t = reverse $ take 4 (reverse (showHex t) ++ (repeat '0'))
>     show8Hex t = reverse $ take 8 (reverse (showHex t) ++ (repeat '0'))

``showHex`` is a helper function that returns the hexadecimal expansion of a natural number.

> showHex :: (Integral n) => n -> String
> showHex n
>   | n < 0  = '-' : showHex (-n)
>   | n == 0 = "0"
>   | otherwise = map toHexDigit (digitsToBase 16 n)
>       where
>         toHexDigit k
>           | k == 0    = '0'
>           | k == 1    = '1'
>           | k == 2    = '2'
>           | k == 3    = '3'
>           | k == 4    = '4'
>           | k == 5    = '5'
>           | k == 6    = '6'
>           | k == 7    = '7'
>           | k == 8    = '8'
>           | k == 9    = '9'
>           | k == 10   = 'a'
>           | k == 11   = 'b'
>           | k == 12   = 'c'
>           | k == 13   = 'd'
>           | k == 14   = 'e'
>           | otherwise = 'f'
> 
> 
> -- digits base b
> digitsToBase :: (Integral n) => n -> n -> [n]
> digitsToBase b k
>   | b <= 1 || k <= 0 = []
>   | otherwise = reverse $ foo k
>       where
>         foo t
>           | t < b = [t]
>           | otherwise = (t`rem`b) : (foo (t`quot`b))

Old stuff:

> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
> 
> 
> -- apply a map to all lines on stdin
> lineFilter :: (String -> String) -> IO ()
> lineFilter f = do
>   xs <- fmap getLines getContents
>   sequence_ $ map (putStrLn . f) xs
> 
> 
> -- split on \n
> getLines :: String -> [String]
> getLines = unfoldr firstLine
>   where
>     firstLine :: String -> Maybe (String, String)
>     firstLine xs = case break (== '\n') xs of
>       ("","")   -> Nothing
>       (as,"")   -> Just (as,"")
>       (as,b:bs) -> Just (as,bs)
