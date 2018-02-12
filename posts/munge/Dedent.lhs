---
title: Dedent
author: nbloomf
date: 2015-07-25
tags: literate-haskell, munge
---

Dedent lines by one space or tab.

> module Dedent where
> 
> import Data.List (lines, intersperse)
> 
> dedent :: String -> String
> dedent = concat . intersperse "\n" . map foo . lines
>   where
>     foo (' ':cs)  = cs
>     foo ('\t':cs) = cs
>     foo x = x
> 
> main :: IO ()
> main = interact dedent
