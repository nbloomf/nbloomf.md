---
title: "Software Tools in Haskell: concat"
subtitle: concatenate files
date: 2016-03-03
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- concat: concatenate files
> module Main where
> 
> import System.Environment (getArgs)
> import System.Exit (exitSuccess)

``concat`` reads a list of file names from the command line and writes the contents of these files, in order, to ``stdout``. It takes no arguments. There is one special case: a single hyphen is interpreted as the name of ``stdin``.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   -- just in case
>   stdin <- getContents
> 
>   let
>     process name = case name of
>       "-"       -> putStr stdin
>       otherwise -> readFile name >>= putStr
> 
>   mapM_ process args
> 
>   exitSuccess
