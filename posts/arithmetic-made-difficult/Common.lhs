---
title: Common
author: nbloomf
date: 2018-01-21
tags: arithmetic-made-difficult, literate-haskell
slug: common
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Common (
>   common, _test_common, main_common
> ) where
> 
> import Testing
> import Booleans
> import Lists
> import Unary
> import NaturalNumbers
> import Filter
> import Cat
> import Reverse
> import Elt
> import Dedupe

Today we'll define a map, $\common(x,y)$, that deletes from $x$ any items that don't also appear in $y$. This doesn't require explicit recursion.

:::::: definition ::
Let $A$ be a set. We define $\common : \lists{A} \times \lists{A}$ by $$\common(x,y) = \filter(\elt(-,y))(x).$$

In Haskell:

> common :: (List t, Equal a) => t a -> t a -> t a
> common x y = filter (\a -> elt a y) x

::::::::::::::::::::

Because $\filter$ is the unique solution to a system of equations, so is $\common$.

:::::: corollary :::
Let $A$ be a set. Then $\common$ is the unique map $f : \lists{A} \times \lists{A} \rightarrow \lists{A}$ satisfying the following equations for all $a \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil,y) = \nil \\
 f(\cons(a,x),y) = \bif{\elt(a,y)}{\cons(a,f(x,y))}{f(x,y)}
\end{array}\right.$$

::: test :::::::::::

> _test_common_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_common_nil t =
>   testName "common(nil,y) == nil" $
>   \y -> eq (common nil y) nil
> 
> 
> _test_common_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_common_cons _ =
>   testName "common(cons(a,x),y) == if(elt(a,y),cons(a,common(x,y)),common(x,y))" $
>   \a x y -> eq
>     (common (cons a x) y)
>     (if elt a y then cons a (common x y) else common x y)

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\cat$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $$\common(\cat(x,y),z) = \cat(\common(x,z),\common(y,z)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \common(\cat(x,y),z) \\
 & = & \filter(\elt(-,z))(\cat(x,y)) \\
 & = & \cat(\filter(\elt(-,z))(x),\filter(\elt(-,z))(y))
 & = & \cat(\common(x,z),\common(y,z)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_common_cat_left _ =
>   testName "common(cat(x,y),z) == cat(common(x,z),common(y,z))" $
>   \x y z -> eq
>     (common (cat x y) z)
>     (cat (common x z) (common y z))

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\rev$ in the first argument.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\common(\rev(x),y) = \rev(\common(x,y)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \common(\rev(x),y) \\
 & = & \filter(\elt(-,y))(\rev(x)) \\
 & = & \rev(\filter(\elt(-,y))(x)) \\
 & = & \rev(\common(x,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: theorem ::::::::

> _test_common_rev_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_rev_left _ =
>   testName "common(rev(x),y) == rev(common(x,y))" $
>   \x y -> eq
>     (common (rev x) y)
>     (rev (common x y))

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\rev$ in the second argument.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\common(x,\rev(y)) = \common(x,y).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \common(x,\rev(y)) \\
 & = & \filter(\elt(-,\rev(y)))(x) \\
 & = & \filter(\elt(-,y))(x) \\
 & = & \common(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_rev_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_rev_right _ =
>   testName "common(x,rev(y)) == common(x,y)" $
>   \x y -> eq
>     (common x (rev y))
>     (common x y)

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\dedupeL$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\common(x,\dedupeL(y)) = \common(x,y).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \common(x,\dedupeL(y)) \\
 & = & \filter(\elt(-,\dedupeL(y)))(x) \\
 & = & \filter(\elt(-,y))(x) \\
 & = $ \common(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_dedupeL_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_dedupeL_right _ =
>   testName "common(x,dedupeL(y)) == common(x,y)" $
>   \x y -> eq
>     (common x (dedupeL y))
>     (common x y)

::::::::::::::::::::
::::::::::::::::::::

(@@@)


Testing
-------

Suite:

> _test_common ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => t a -> Int -> Int -> IO ()
> _test_common t maxSize numCases = do
>   testLabel1 "common" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_common_nil t)
>   runTest args (_test_common_cons t)
>   runTest args (_test_common_cat_left t)
>   runTest args (_test_common_rev_left t)
>   runTest args (_test_common_rev_right t)
>   runTest args (_test_common_dedupeL_right t)

Main:

> main_common :: IO ()
> main_common = do
>   _test_common (nil :: ConsList Bool)  20 100
>   _test_common (nil :: ConsList Unary) 20 100
