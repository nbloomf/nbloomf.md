---
title: Software Tools in Haskell: line number
subtitle: number lines on stdin
author: nbloomf
---

This is another utility intended for use with ``pslineprint``: it prepends lines on ``stdin`` with line numbers.

By default, this program separates the line number from the line contents by a tab; the output is tab-delimited text. This reflects the fact that the line number is semantically distinct from the line contents. The ``--pad`` option instead separates the numbers from the contents by a space, and also left-pads the numbers so that they are vertically aligned and right-justified. Finally, the ``--from`` option allows the user to specify the number of the first line (natural numbers only).

We made tab-separated output the default because it is the simplest; we can march down the list of lines on ``stdin`` and send them to ``stdout`` with the numer prefixed. We only need to keep track of the current line number. Nicely padded line numbers with spaces, however, require us to know in advance the total number of lines required before we can begin producing output.


```haskell
-- linenumber: number lines on stdin

module Main where

import System.Exit (exitSuccess, exitFailure)
import System.Environment (getArgs)
import STH.Lib
  (reportErrorMsgs, readDecimalNat, getLines,
   putStrLns, padToByBefore)

data Mode = Tab | Pad

main :: IO ()
main = do
  args <- getArgs

  (mode,from) <- do
    let
      (m,rest) = case args of
        ("--pad":xs) -> (Pad, xs)
        xs           -> (Tab, xs)

    case rest of
      ["--from",k] -> case readDecimalNat k of
        Nothing -> argErr >> exitFailure
        Just t  -> return (m,t)
      otherwise -> return (m,1)

  lns <- fmap ((zip [from..]) . getLines) getContents

  case mode of
    Tab -> do
      let wr (a,str) = show a ++ "\t" ++ str
      putStrLns $ map wr lns

    Pad -> do
      let
        len = case lns of
          [] -> 0
          zs -> length $ show $ fst $ last zs
        pad n = padToByBefore len ' ' (show n)
        wr (a,str) = pad a ++ " " ++ str
      putStrLns $ map wr lns

  exitSuccess



argErr :: IO ()
argErr = reportErrorMsgs
  [ "usage:"
  , "  linenumber       : prepend line numbers (tab separated)"
  , "  linenumber --pad : prepend line numbers (padded with spaces)"
  , "options:"
  , "  --from NAT : start numbering at NAT; default is 1"
  ]
```


This program uses one new library function: ``padToByBefore``, the companion of ``padToByAfter``.


```haskell
padToByBefore :: Int -> a -> [a] -> [a]
padToByBefore k z xs = reverse $ padToByAfter k z (reverse xs)
```
