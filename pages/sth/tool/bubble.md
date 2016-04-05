---
title: Software Tools in Haskell: bubble
subtitle: (bubble)sort lines on stdin
author: nbloomf
---

This is a horrible sorting program which should never be used by anyone. But in the interest of completeness, here it is all the same: bubblesort. Because the bubble sort algorithm is so terrible, I won't bother giving this program useful options (we'll write a for-real sorting tool next).

Some traditional sorting algorithms are a little awkward to write in Haskell due to immutability. The bottom line is that we can't "update" a data structure in place in memory; instead Haskell creates a new copy of the data structure with changes applied. So some simple ideas like "swap the entries at positions $i$ and $j$", essential to efficient implementations of quicksort and shellsort, are difficult to express.

That said, here's my attempt at bubblesort.


```haskell
bubble :: (Ord a) => [a] -> [a]
bubble xs = case accum False [] xs of
  (True,  ys) -> bubble ys
  (False, ys) -> ys
  where
    accum p zs (x:y:ys) = if x <= y
      then accum p    (x:zs) (y:ys)
      else accum True (y:zs) (x:ys)
    accum p zs ys  = (p, reverse $ (reverse ys) ++ zs)
```


The ``accum`` helper function marches down a list swapping elements which are out of order. It also keeps track of whether or not any swaps are made. Then ``bubble`` applies ``accum`` over and over again until no swaps are made. Interestingly, this makes ``bubble`` linear on lists which are already sorted. And I think (but am not certain) that if each element of the input list is at most $k$ indices out of place that the complexity of ``bubble`` is $\mathcal{O}(kn)$. This is not to say that ``bubble`` is the Right Way to sort things; in my testing it is excruciatingly slow even on small lists (1000 items).

The main program simply applies ``bubble`` to the contents of ``stdin``. Note that since we use the standard ``Ord`` instance for strings, ``bubble`` sorts by unicode code point.


```haskell
-- sth-bubble: (bubble)sort lines on stdin

module Main where

import System.Exit (exitSuccess)
import STH.Lib (putStrLns, bubble, getLines)

main :: IO ()
main = do
  lns <- fmap getLines getContents
  mapM_ putStrLn $ bubble lns
  exitSuccess
```
