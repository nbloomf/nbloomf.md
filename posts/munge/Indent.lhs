---
title: Indent
author: nbloomf
date: 2015-07-25
tags: literate-haskell, munge
---

Indent lines by one space.

> module Indent where
> 
> import Data.List (lines, intersperse)
> 
> indent :: String -> String
> indent = concat . intersperse "\n" . map (' ':) . lines
> 
> main :: IO ()
> main = interact indent
