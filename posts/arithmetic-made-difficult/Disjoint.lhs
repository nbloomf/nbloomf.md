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
> import And
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import Reverse
> import Cat
> import Dedupe
> import Common

Today we'll define a relation to detect when two lists have no items in common.

:::::: definition ::
We define $\disjoint : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\disjoint(x,y) = \isnil(\common(x,y)).$$

In Haskell:

> disjoint :: (List t, Equal a) => t a -> t a -> Bool
> disjoint x y = isNil (common x y)

::::::::::::::::::::

$\nil$ is disjoint with every list.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\disjoint(\nil,x) = \btrue.$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \disjoint(\nil,x) \\
 & = & \isnil(\common(\nil,x)) \\
 & = & \isnil(\nil) \\
 &     \href{@head-tail@#thm-isnil-nil}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_disjoint_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_disjoint_nil _ =
>   testName "disjoint(nil,x) == true" $
>   \x -> eq (disjoint nil x) true

::::::::::::::::::::
::::::::::::::::::::

$\disjoint$ interacts with $\dedupeL$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\disjoint(x,\dedupeL(y)) = \disjoint(x,y).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \disjoint(x,\dedupeL(y)) \\
 & = & \isnil(\common(x,\dedupeL(y))) \\
 & = & \isnil(\common(x,y)) \\
 & = & \disjoint(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_disjoint_dedupeL_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_disjoint_dedupeL_right _ =
>   testName "disjoint(x,dedupeL(y)) == disjoint(x,y)" $
>   \x y -> eq
>     (disjoint x (dedupeL y))
>     (disjoint x y)

::::::::::::::::::::
::::::::::::::::::::

Disjoint interacts with $\cat$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $$\disjoint(\cat(x,y),z) = \band(\disjoint(x,z),\disjoint(y,z)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \disjoint(\cat(x,y),z) \\
 & = & \isnil(\common(\cat(x,y),z)) \\
 & = & \isnil(\cat(\common(x,z),\common(y,z))) \\
 & = & \band(\isnil(\common(x,z)),\isnil(\common(y,z))) \\
 & = & \band(\disjoint(x,z),\disjoint(y,z))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_disjoint_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_disjoint_cat_left _ =
>   testName "disjoint(cat(x,y),z) == and(disjoint(x,z),disjoint(y,z))" $
>   \x y z -> eq
>     (disjoint (cat x y) z)
>     (and (disjoint x z) (disjoint y z))

::::::::::::::::::::
::::::::::::::::::::

$\disjoint$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\disjoint(x,\rev(y)) = \disjoint(x,y).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \disjoint(x,\rev(y)) \\
 & = & \isnil(\common(x,\rev(y))) \\
 & = & \isnil(\common(x,y)) \\
 & = & \disjoint(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_disjoint_rev_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_disjoint_rev_right _ =
>   testName "disjoint(x,rev(y)) == disjoint(x,y)" $
>   \x y -> eq
>     (disjoint x (rev y))
>     (disjoint x y)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_disjoint ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => Int -> Int -> t a -> IO ()
> _test_disjoint size cases t = do
>   testLabel1 "disjoint" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_disjoint_nil t)
>   runTest args (_test_disjoint_dedupeL_right t)
>   runTest args (_test_disjoint_cat_left t)
>   runTest args (_test_disjoint_rev_right t)

Main:

> main_disjoint :: IO ()
> main_disjoint = do
>   _test_disjoint 20 100 (nil :: ConsList Bool)
>   _test_disjoint 20 100 (nil :: ConsList Unary)
