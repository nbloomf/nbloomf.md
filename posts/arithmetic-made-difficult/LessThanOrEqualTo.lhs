---
title: Less than or equal to
author: nbloomf
date: 2017-04-02
tags: arithmetic-made-difficult, literate-haskell
---

> module LessThanOrEqualTo
>  ( leq
>  ) where
> 
> import Nat
> import PrimitiveRecursion
> import Plus
> import Times
> 
> import Test.QuickCheck

> leq :: Nat -> Nat -> Maybe Nat
> leq = primRec phi mu
>   where
>     phi x = Just x
>
>     mu _ _ w = do
>       c <- w
>       case c of
>         Z   -> Nothing
>         N d -> Just d

> isLeq :: Nat -> Nat -> Bool
> isLeq a b = case leq a b of
>   Nothing -> False
>   Just _  -> True
