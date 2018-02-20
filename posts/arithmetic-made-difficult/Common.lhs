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
> import And
> import Unary
> import Lists
> import Snoc
> import Reverse
> import Cat
> import Filter
> import Elt
> import Sublist
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
> _test_common_nil _ =
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
 & = & \cat(\filter(\elt(-,z))(x),\filter(\elt(-,z))(y)) \\
 & = & \cat(\common(x,z),\common(y,z))
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

::: test :::::::::::

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

$\common$ interacts with $\dedupeL$ in the second argument.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\common(x,\dedupeL(y)) = \common(x,y).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \common(x,\dedupeL(y)) \\
 & = & \filter(\elt(-,\dedupeL(y)))(x) \\
 & = & \filter(\elt(-,y))(x) \\
 & = & \common(x,y)
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

$\common$ interacts with $\dedupeL$ in the left argument.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\common(\dedupeL(x),y) = \dedupeL(\common(x,y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \common(\dedupeL(x),y) \\
 & = & \filter(\elt(-,y))(\dedupeL(x)) \\
 & = & \dedupeL(\filter(\elt(-,y))(x)) \\
 & = & \dedupeL(\common(x,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_dedupeL_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_dedupeL_left _ =
>   testName "common(dedupeL(x),y) == dedupeL(common(x,y))" $
>   \x y -> eq
>     (common (dedupeL x) y)
>     (dedupeL (common x y))

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have $$\common(\snoc(a,x),y) = \bif{\elt(a,y)}{\snoc(\common(x,y))}{\common(x,y)}.$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \common(\snoc(a,x),y) \\
 & = & \filter(\elt(-,y))(\snoc(a,x)) \\
 & = & \bif{\elt(a,y)}{\snoc(a,\filter(\elt(-,y))(x))}{\filter(\elt(-,y))(x)} \\
 & = & \bif{\elt(a,y)}{\snoc(a,\common(x,y))}{\common(x,y)}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_common_snoc _ =
>   testName "common(snoc(a,x),y) == if(elt(a,y),snoc(a,common(x,y)),common(x,y))" $
>   \a x y -> eq
>     (common (snoc a x) y)
>     (if elt a y then snoc a (common x y) else common x y)

::::::::::::::::::::
::::::::::::::::::::

We can simplify $\common$ if the second argument is a singleton.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\common(x,\cons(a,\nil)) = \filter(\beq(a,-))(x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \common(x,\cons(a,\nil)) \\
 & = & \filter(\elt(-,\cons(a,\nil)))(x) \\
 & = & \filter(\beq(-,a))(x) \\
 & = & \filter(\beq(a,-))(x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_singleton_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_common_singleton_right _ =
>   testName "common(x,cons(a,nil)) == filter(eq(a,-))(x)" $
>   \a x -> eq
>     (common x (cons a nil))
>     (filter (eq a) x)

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\elt$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$, we have $$\elt(a,\common(x,y)) = \band(\elt(a,x),\elt(a,y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \elt(a,\common(x,y)) \\
 & = & \elt(a,\filter(\elt(-,y))(x)) \\
 & = & \band(\elt(a,y),\elt(a,x)) \\
 &     \href{@and@#thm-and-commutative}
   = & \band(\elt(a,x),\elt(a,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_elt_distribute :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_common_elt_distribute _ =
>   testName "elt(a,common(x,y)) == and(elt(a,x),elt(a,y))" $
>   \a x y -> eq
>     (elt a (common x y))
>     (and (elt a x) (elt a y))

::::::::::::::::::::
::::::::::::::::::::

As a consequence, $\common$ is *almost* commutative.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$, we have $$\elt(a,\common(x,y)) = \elt(a,\common(y,x)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \elt(a,\common(x,y)) \\
 & = & \band(\elt(a,x),\elt(a,y)) \\
 &     \href{@and@#thm-and-commutative}
   = & \band(\elt(a,y),\elt(a,x)) \\
 & = & \elt(a,\common(y,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_elt_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_common_elt_commutative _ =
>   testName "elt(a,common(x,y)) == elt(a,common(y,x))" $
>   \a x y -> eq
>     (elt a (common x y))
>     (elt a (common y x))

::::::::::::::::::::
::::::::::::::::::::

$\common$ is associative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$, we have $$\common(x,\common(y,z)) = \common(\common(x,y),z).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \common(\nil,\common(y,z)) \\
 & = & \nil \\
 & = & \common(\nil,z) \\
 & = & \common(\common(\nil,y),z)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ and $z$ for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \common(\cons(a,x),\common(y,z)) \\
 & = & \filter(\elt(-,\common(y,z)))(\cons(a,x)) \\
 & = & \bif{\elt(a,\common(y,z))}{\cons(a,\filter(\elt(-,\common(y,z)))(x))}{\filter(\elt(-,\common(y,z)))(x)} \\
 & = & \bif{\elt(a,\common(y,z))}{\cons(a,\common(x,\common(y,z)))}{\common(x,\common(y,z))} \\
 & = & \bif{\elt(a,\filter(\elt(-,z))(y))}{\cons(a,\common(x,\common(y,z)))}{\common(x,\common(y,z))} \\
 & = & \bif{\band(\elt(a,z),\elt(a,y))}{\cons(a,\common(x,\common(y,z)))}{\common(x,\common(y,z))} \\
 & = & \bif{\band(\elt(a,y),\elt(a,z))}{\cons(a,\common(\common(x,y),z))}{\common(\common(x,y),z)} \\
 &     \href{@and@#thm-and-if-hyp}
   = & \bif{\elt(a,y)}{\bif{\elt(a,z)}{\cons(a,\common(\common(x,y),z))}{\common(\common(x,y),z)}}{\common(\common(x,y),z)} \\
 & = & \bif{\elt(a,y)}{\bif{\elt(a,z)}{\cons(a,\filter(\elt(-,z))(\common(x,y)))}{\filter(\elt(-,z))(\common(x,y))}}{\common(\common(x,y),z)} \\
 & = & \bif{\elt(a,y)}{\filter(\elt(-,z))(\cons(a,\common(x,y)))}{\common(\common(x,y),z)} \\
 & = & \bif{\elt(a,y)}{\filter(\elt(-,z))(\cons(a,\common(x,y)))}{\filter(\elt(-,z))(\common(x,y))} \\
 & = & \bif{\elt(a,y)}{\filter(\elt(-,z))(\cons(a,\filter(\elt(-,y))(x)))}{\filter(\elt(-,z))(\filter(\elt(-,y))(x))} \\
 & = & \filter(\elt(-,z))(\bif{\elt(a,y)}{\cons(a,\filter(\elt(-,y))(x))}{\filter(\elt(-,y))(x)}) \\
 & = & \filter(\elt(-,z))(\filter(\elt(-,y))(\cons(a,x))) \\
 & = & \common(\filter(\elt(-,y))(\cons(a,x)),z) \\
 & = & \common(\common(\cons(a,x),y),z)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_associative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_common_associative _ =
>   testName "common(x,common(y,z)) == common(common(x,y),z)" $
>   \x y z -> eq
>     (common x (common y z))
>     (common (common x y) z)

::::::::::::::::::::
::::::::::::::::::::

$\common$ is a sublist.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\sublist(\common(x,y),x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \sublist(\common(x,y),x) \\
 & = & \sublist(\filter(\elt(-,y))(x),x) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_sublist _ =
>   testName "sublist(common(x,y),x)" $
>   \x y -> sublist (common x y) x

::::::::::::::::::::
::::::::::::::::::::

$\common$ interacts with $\cat$ in the second argument.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\common(x,\cat(y,x)) = x.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \common(\nil,\cat(y,\nil)) \\
 & = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \common(\cons(a,x),\cat(y,\cons(a,x))) \\
 & = & \bif{\elt(a)(\cat(y,\cons(a,x)))}{\cons(a,\common(x,\cat(y,\cons(a,x))))}{\common(x,\cat(y,\cons(a,x)))} \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \bif{\elt(a)(\cat(y,\cons(a,x)))}{\cons(a,\common(x,\cat(\snoc(a,y),x)))}{\common(x,\cat(y,\cons(a,x)))} \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \bif{\elt(a)(\cat(y,\cons(a,x)))}{\cons(a,\common(x,\cat(\snoc(a,y),x)))}{\common(x,\cat(\snoc(a,y),x))} \\
 & = & \bif{\elt(a)(\cat(y,\cons(a,x)))}{\cons(a,x)}{\common(x,\cat(\snoc(a,y),x))} \\
 & = & \bif{\elt(a)(\cat(y,\cons(a,x)))}{\cons(a,x)}{x} \\
 & = & \bif{\btrue}{\cons(a,x)}{x} \\
 &     \href{@booleans@#cor-if-true}
   = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_common_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_common_cat_right _ =
>   testName "common(x,cat(y,x)) == x" $
>   \x y -> eq (common x (cat y x)) x

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_common ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => t a -> Int -> Int -> IO ()
> _test_common t size cases = do
>   testLabel1 "common" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_common_nil t)
>   runTest args (_test_common_cons t)
>   runTest args (_test_common_cat_left t)
>   runTest args (_test_common_rev_left t)
>   runTest args (_test_common_rev_right t)
>   runTest args (_test_common_dedupeL_right t)
>   runTest args (_test_common_dedupeL_left t)
>   runTest args (_test_common_snoc t)
>   runTest args (_test_common_singleton_right t)
>   runTest args (_test_common_elt_distribute t)
>   runTest args (_test_common_elt_commutative t)
>   runTest args (_test_common_associative t)
>   runTest args (_test_common_sublist t)
>   runTest args (_test_common_cat_right t)

Main:

> main_common :: IO ()
> main_common = do
>   _test_common (nil :: ConsList Bool)  20 100
>   _test_common (nil :: ConsList Unary) 20 100
