---
title: Software Tools in Haskell: wye
subtitle: write stdin to files and stdout
author: nbloomf
---

``wye`` acts like the standard tool ``tee``; it writes ``stdin`` to one or more files as well as ``stdout``. It takes one argument: ``--append`` opens the given files in append mode rather than (default) overwrite mode. Since this program processes lines from ``stdin`` one at a time, we use file handles rather than writing files all in one go. We have to be sure to close these file handles before exiting.


```haskell
-- wye: write stdin to files and stdout

module Main where

import System.Exit (exitSuccess)
import System.Environment (getArgs)
import System.IO
  (openFile, hClose, IOMode(AppendMode,WriteMode), hPutStrLn)
import STH.Lib (lineFilterIO)

main :: IO ()
main = do
  args <- getArgs

  -- interpret arguments
  handles <- do
    let
      (mode,rest) = case args of
        ("--append":xs) -> (AppendMode,xs)
        xs              -> (WriteMode, xs)

    mapM (\name -> openFile name mode) rest


  let
    split str = do
      putStrLn str
      mapM_ (\handle -> hPutStrLn handle str) handles

  lineFilterIO split

  mapM_ hClose handles

  exitSuccess
```
