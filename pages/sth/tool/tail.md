---
title: Software Tools in Haskell: tail
subtitle: get the last k lines or chars from stdin
author: nbloomf
---

The version of ``tail`` on my system accepts 10 optional arguments, not including ``--help`` and ``--version``. I am sure that there are very good reasons for these. But this version will take only two: ``--char`` specifies that we want to take the last few characters, rather than lines, and an optional integer argument specifies the number to take.

We use a data type, ``Mode``, to represent the processing mode (lines or chars). Most of the complexity is in reading arguments and reporting errors.


```haskell
-- tail: get the last k lines or chars from stdin

module Main where

import System.Exit (exitSuccess, exitFailure)
import System.Environment (getArgs)
import STH.Lib
  (readDecimalNat, reportErrorMsgs,
   getLines, putStrLns)

data Mode = Chars | Lines

main :: IO ()
main = do
  args <- getArgs

  (mode,k) <- do
    (flag,rest) <- case args of
      ("--char":xss) -> return (Chars,xss)
      xss            -> return (Lines,xss)

    case rest of
      []   -> return (flag,10)
      [xs] -> case readDecimalNat xs of
                Nothing -> argErr >> exitFailure
                Just t  -> return (flag,t)
      _    -> argErr >> exitFailure

  let
    getTail = reverse . take k . reverse

  case mode of
    Chars -> fmap getTail getContents
               >>= putStr
    Lines -> fmap (getTail . getLines) getContents
               >>= putStrLns

  exitSuccess


argErr :: IO ()
argErr = reportErrorMsgs
  [ "usage:"
  , "  tail     : send the last 10 lines of stdin to stdout"
  , "  tail INT : send the last INT lines of stdin to stdout"
  , "options:"
  , "  --char : get chars instead of lines"
  ]
```
