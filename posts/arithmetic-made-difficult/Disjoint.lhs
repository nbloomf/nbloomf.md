---
title: Disjoint
author: nbloomf
date: 2018-01-22
tags: arithmetic-made-difficult, literate-haskell
slug: disjoint
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Disjoint (
>   disjoint, _test_disjoint, main_disjoint
> ) where
> 
> import Testing
> import Booleans
> import Lists
> import HeadAndTail
> import Common

Today we'll define a relation to detect when two lists have no items in common.

:::::: definition ::
We define $\disjoint : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\disjoint(x,y) = \isnil(\common(x,y)).$$

In Haskell:

> disjoint :: (List t, Equal a) => t a -> t a -> Bool
> disjoint x y = isNil (common x y)

::::::::::::::::::::

(@@@)


Testing
-------

> _test_disjoint = undefined

> main_disjoint :: IO ()
> main_disjoint = return ()
