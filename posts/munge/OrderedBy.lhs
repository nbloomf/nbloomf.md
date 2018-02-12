---
title: Ordered By
author: nbloomf
date: 2018-02-07
tags: literate-haskell, munge
---

Here's a task I haven't found a good pipeline for: showing that some lines in a file are in a prescribed order -- but not necessarily alphabetical/numerical/asciibetical order. The main motivating case is checking the order of imports in a Haskell module, but another example is finding the first word in an alphabetized list that doesn't appear in an alphabetized dictionary. Essentially, thinking of two files as lists of lines, find the longest suffix of one list that is not a sublist of the other.

> module OrderedBy where
> 
> import System.Environment

This function is shaped like a fold on the "dictionary".

> orderedBy :: (Eq a) => [a] -> [a] -> [a]
> orderedBy as bs = foldl checkHead as bs
>   where
>     checkHead :: (Eq a) => [a] -> a -> [a]
>     checkHead []     x = []
>     checkHead (y:ys) x = if x == y then ys else y:ys

Usage is simple: we pass the path to the "dictionary" as an argument, and look for the list to be checked on stdin.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   case args of
>     ["--dict",path] -> do
>       dict <- fmap lines $ readFile path
>       words <- fmap lines getContents
>       mapM_ putStrLn $ orderedBy words dict
> 
>     _ -> do
>       putStrLn "usage: orderedby --dict PATH"
