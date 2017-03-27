---
title: Software Tools in Haskell: wye
subtitle: write stdin to files and stdout
date: 2016-03-04
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-03-04-software-tools-in-haskell-wye.lhs) into GHCi and play along. As usual, we start with some imports.

> -- wye: write stdin to files and stdout
> module Main where
> 
> import System.Exit (exitSuccess)
> import System.Environment (getArgs)
> import Data.List (unfoldr)
> import System.IO
>   ( openFile, hClose
>   , IOMode(AppendMode,WriteMode), hPutStrLn
>   )

``wye`` acts like the standard tool ``tee``; it writes ``stdin`` to one or more files as well as ``stdout``. It takes one argument: ``--append`` opens the given files in append mode rather than (default) overwrite mode. Since this program processes lines from ``stdin`` one at a time, we use file handles rather than writing files all in one go. We have to be sure to close these file handles before exiting.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   -- interpret arguments
>   handles <- do
>     let
>       (mode,rest) = case args of
>         ("--append":xs) -> (AppendMode,xs)
>         xs              -> (WriteMode, xs)
> 
>     mapM (\name -> openFile name mode) rest
> 
> 
>   let
>     split str = do
>       putStrLn str
>       mapM_ (\handle -> hPutStrLn handle str) handles
> 
>   lineFilterIO split
> 
>   mapM_ hClose handles
> 
>   exitSuccess

``wye`` is useful for inspecting data as it flows through a pipeline, maybe for debugging purposes. For instance, if the final output of a pipeline like

    foo | bar | baz | qux

is not what we expect, we can inspect the intermediate data with

    foo | wye a.txt | bar | wye b.txt | baz | wye c.txt | qux


Old Stuff
---------

> lineFilterIO :: (String -> IO ()) -> IO ()
> lineFilterIO f = do
>   xs <- fmap getLines getContents
>   sequence_ $ map f xs
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
