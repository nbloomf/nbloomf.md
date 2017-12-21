---
title: "Software Tools in Haskell: charfullwidth"
subtitle: replace chars with fullwidth equivalents
date: 2016-02-17
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-charfullwidth: replace characters with fullwidth equivalents
> module Main where
> 
> import System.Exit (exitSuccess)

Replacing "normal" characters with fullwidth forms is much simpler. We reuse the structure of ``copy --char``, with a filter to map characters.

> main :: IO ()
> main = do
>   charFilter (map toFullwidth)
>   exitSuccess

And the map:

> toFullwidth :: Char -> Char
> toFullwidth = applyListMap full
>   where
>     full =
>       [ ('!','！'), ('"','＂'),  ('#','＃'), ('$','＄'), ('%','％')
>       , ('&','＆'), ('\'','＇'), ('(','（'), (')','）'), ('*','＊')
>       , ('+','＋'), (',','，'),  ('-','－'), ('.','．'), ('/','／')
>       , ('0','０'), ('1','１'),  ('2','２'), ('3','３'), ('4','４')
>       , ('5','５'), ('6','６'),  ('7','７'), ('8','８'), ('9','９')
>       , (':','：'), (';','；'),  ('<','＜'), ('=','＝'), ('>','＞')
>       , ('?','？'), ('@','＠'),  ('A','Ａ'), ('B','Ｂ'), ('C','Ｃ')
>       , ('D','Ｄ'), ('E','Ｅ'),  ('F','Ｆ'), ('G','Ｇ'), ('H','Ｈ')
>       , ('I','Ｉ'), ('J','Ｊ'),  ('K','Ｋ'), ('L','Ｌ'), ('M','Ｍ')
>       , ('N','Ｎ'), ('O','Ｏ'),  ('P','Ｐ'), ('Q','Ｑ'), ('R','Ｒ')
>       , ('S','Ｓ'), ('T','Ｔ'),  ('U','Ｕ'), ('V','Ｖ'), ('W','Ｗ')
>       , ('X','Ｘ'), ('Y','Ｙ'),  ('Z','Ｚ'), ('[','［'), ('\\','＼')
>       , (']','］'), ('^','＾'),  ('_','＿'), ('`','｀'), ('a','ａ')
>       , ('b','ｂ'), ('c','ｃ'),  ('d','ｄ'), ('e','ｅ'), ('f','ｆ')
>       , ('g','ｇ'), ('h','ｈ'),  ('i','ｉ'), ('j','ｊ'), ('k','ｋ')
>       , ('l','ｌ'), ('m','ｍ'),  ('n','ｎ'), ('o','ｏ'), ('p','ｐ')
>       , ('q','ｑ'), ('r','ｒ'),  ('s','ｓ'), ('t','ｔ'), ('u','ｕ')
>       , ('v','ｖ'), ('w','ｗ'),  ('x','ｘ'), ('y','ｙ'), ('z','ｚ')
>       , ('{','｛'), ('|','｜'),  ('}','｝'), ('~','～'), (' ','　')
>       ]

This probably looks terrible in your browser because unicode coverage. The ``applyListMap`` function treats a list of pairs like a mapping.

> applyListMap :: (Eq a) => [(a,a)] -> a -> a
> applyListMap zs x = case lookup x zs of
>   Nothing -> x
>   Just y  -> y
> 
> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
