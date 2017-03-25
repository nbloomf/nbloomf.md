---
title: Software Tools in Haskell: glyphcount
subtitle: count glyphs on stdin
date: 2016-02-14
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-02-14-software-tools-in-haskell-glyphcount.lhs) into GHCi and play along. As usual, we start with some imports.

> -- sth-glyphcount: count glyphs on stdin
> module Main where
> 
> import System.Exit (exitSuccess)
> import Data.Char (isMark)
> import Data.List (unfoldr)
> import Data.Foldable (foldl')

When we wrote [``count``](/posts/2016-02-11-software-tools-in-haskell-count.html), we saw that there is a serious ambiguity in the meaning of "character" in Unicode. On one hand Unicode defines a list of character code points, but on the other hand sequences of code points do not necessarily correspond to symbols on the screen in the way ASCII characters do. In fact there is a [Unicode Technical Report](http://www.unicode.org/reports/tr17/#CharactersVsGlyphs) which addresses this ambiguity; unfortunately the conclusion there is that

<blockquote>The correspondence between glyphs and characters is generally not one-to-one, and cannot be predicted from the text alone. <cite>Unicode Technical Report #17</cite></blockquote>

Given this difficulty, we will make a simplifying assumption. **A "glyph" is a non-combining character followed by zero or more combining characters.** Fortunately there is a standard library function, ``isMark``, which detects which characters are combining diacritics. The ``getGlyphs`` function splits a string into a list of glyphs.

> -- break a string into a list of "glyphs"
> getGlyphs :: String -> [String]
> getGlyphs = unfoldr firstGlyph
>   where
>     firstGlyph :: String -> Maybe (String, String)
>     firstGlyph "" = Nothing
>     firstGlyph (x:xs) = if isMark x
>       then Just $ break (not . isMark) (x:xs)
>       else do
>         let (as,bs) = break (not . isMark) xs
>         Just (x:as, bs)
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

Now the main function is much like that of ``count``.

> main :: IO ()
> main = do
>   charFilter (show . count . getGlyphs)
>   putNewLine
>   exitSuccess
