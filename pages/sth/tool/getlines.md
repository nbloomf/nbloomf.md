---
title: Software Tools in Haskell: getlines
subtitle: extract lines from stdin by index
author: nbloomf
---

This program is not an example from *Software Tools*; I wrote it to test some functionality that will eventually go into the print program -- namely, parsing sets of integers.

``getlines`` does one thing: it takes a set of integers as an argument, and extracts from ``stdin`` the lines whose indices (counting from 1) are in the given set. For instance,

    getlines "6"

extracts the line at index 6. We can also specify ranges, like

    getlines "1-5"

which extracts lines 1, 2, 3, 4, and 5, as well as skip counts, like

    getlines "2+3"

which extracts every third line starting with the second (i.e. 2, 5, 8, and so on). We can give several rules separated by commas, and the indices specified will be extracted in order. So

    getlines "7-9,1,2"

will extract lines 1, 2, 7, 8, and 9, in that order. We can give more than one integer set argument, and each will be considered in turn with the results concatenated. So

    getlines "1,2" "1,2" "1,2"

extracts lines 1, 2, 1, 2, 1, and 2, in that order.

We define a data type for each kind of integer set: single integers, ranges, and skip counts.


```haskell
data IntSet
  = Single Int
  | Range  Int Int
  | Skip   Int Int
  deriving (Show)

inIntSet :: Int -> [IntSet] -> Bool
inIntSet k ms = or $ map (inIntSet' k) ms
  where
    inIntSet' :: Int -> IntSet -> Bool
    inIntSet' k (Single m)  = k == m
    inIntSet' k (Range a b) = (a <= k) && (k <= b)
    inIntSet' k (Skip a b)  = (k >= a) && ((k-a)`rem`b == 0)

readIntSet :: String -> Maybe (Int -> Bool)
readIntSet xs = do
  cs <- readIntSet' xs
  return (\k -> inIntSet k cs)

readIntSet' :: String -> Maybe [IntSet]
readIntSet' = sequence . map oneIntSeq . breakAt ','
  where
    oneIntSeq :: String -> Maybe IntSet
    oneIntSeq "" = Nothing
    oneIntSeq xs = case readDecimalNat xs of
      Just k  -> Just $ Single k
      Nothing -> case map readDecimalNat $ breakAt '-' xs of
        [Just a, Just b] -> Just $ Range a b
        otherwise        -> case map readDecimalNat $ breakAt '+' xs of
          [Just a, Just b] -> Just $ Skip a b
          otherwise        -> Nothing
```


This code is in a separate library module which only exports one function: ``readIntSet``. That function takes the string representation of a set and returns a function that detects whether a given integer is in the set specified. Compared to representing a set of integers as a set, this makes representing large ranges more efficient and makes representing infinite sets (like skip lists) possible.

Next we write a library function that extracts items from a list.


```haskell
getEltsByIndex :: (Int -> Bool) -> [a] -> [a]
getEltsByIndex p xs = map snd $ filter (p . fst) $ zip [1..] xs
```


Finally, the main program is simple enough. We take one optional argument, ``--asacc``, which interprets "lines" using the ASA carriage control format.


```haskell
-- getlines: extract lines from stdin by index

module Main where

import System.Exit (exitSuccess, exitFailure)
import System.Environment (getArgs)
import STH.Lib
  (getEltsByIndex, reportErrorMsgs, readIntSet,
   putStrLns, getLines, readCCLines, renderCCLine,
   putCCLns)


data Mode = Lines | ASACC


main :: IO ()
main = do
  args <- getArgs

  -- interpret arguments
  (mode,tests) <- do
    let
      (flag,rest) = case args of
        ("--asacc":zs) -> (ASACC, zs)
        zs             -> (Lines, zs)

    ps <- case sequence $ map readIntSet rest of
      Just xs -> return xs
      Nothing -> argErr >> exitFailure

    return (flag,ps)

  let get xs p = getEltsByIndex p xs

  case mode of
    Lines -> do
      lines <- fmap getLines getContents
      putStrLns $ concatMap (get lines) tests
    ASACC -> do
      lines <- fmap readCCLines getContents
      case lines of
        Nothing -> corrErr >> exitFailure
        Just zs -> putCCLns $ concatMap (get zs) tests

  exitSuccess


argErr :: IO ()
argErr = reportErrorMsgs
  [ "usage:"
  , "  getlines INTSET ... : extract lines from stdin at indices in RANGE (sorted)"
  , "options:"
  , "  --asacc : read as ASA carriage control lines"
  ]


corrErr :: IO ()
corrErr = reportErrorMsgs
  [ "corrupt input" ]
```
