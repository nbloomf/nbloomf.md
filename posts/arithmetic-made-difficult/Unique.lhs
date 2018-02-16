---
title: Unique
author: nbloomf
date: 2017-05-26
tags: arithmetic-made-difficult, literate-haskell
slug: unique
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Unique
>   ( unique, _test_unique, main_unique
>   ) where
> 
> import Testing
> import Tuples
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Plus
> import LessThanOrEqualTo
> import Lists
> import ConsumingFold
> import Snoc
> import Reverse
> import Cat
> import Length
> import Map
> import UnfoldN
> import Range
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Sublist
> import Select

Today we'll introduce a boolean function $\unique$ to detect whether or not a list has any duplicate items. As usual, we'd like to define $\unique$ as a fold. The signature needs to be $$\lists{A} \rightarrow \bool.$$ How can we do this? Intuitively, we might say

1. $\nil$ is unique, and
2. $\cons(a,x)$ is unique if $x$ is unique and $a$ does not appear in $x$.

Note that $\unique$ will need to "have it's cake and eat it too"; that is, when testing $\cons(a,x)$ for uniqueness we have to check that $x$ is unique (eat the cake) *and* check that $a$ does not appear in $x$ (have the cake). We had a similar problem when we defined $\tails$; the solution there was to use consuming fold, so that's what we'll do here.

:::::: definition ::
Let $A$ be a set. Define $\sigma : A \times \lists{A} \times \bool \rightarrow \bool$ by $$\sigma(a,x,p) = \band(\bnot(\elt(a,x)),p).$$ We then define $\unique : \lists{A} \rightarrow \bool$ by $$\unique = \cfoldr{\btrue}{\sigma}.$$

In Haskell:

> unique :: (List t, Equal a) => t a -> Bool
> unique = cfoldr true sigma
>   where
>     sigma a x p = and (not (elt a x)) p

::::::::::::::::::::

Since $\unique$ is defined as a $\cfoldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\unique$ is the unique map $f : \lists{A} \rightarrow \bool$ satisfying the following system of equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \btrue \\
 f(\cons(a,x)) = \band(\bnot(\elt(a,x)),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_unique_nil :: (List t, Equal a)
>   => t a -> Test Bool
> _test_unique_nil t =
>   testName "unique(nil) == true" $
>    eq (unique (nil `withTypeOf` t)) true
> 
> 
> _test_unique_cons :: (List t, Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_unique_cons _ =
>   testName "unique(cons(a,x)) == and(not(elt(a,x)),unique(x))" $
>    \a x -> eq (unique (cons a x)) (and (not (elt a x)) (unique x))

::::::::::::::::::::
::::::::::::::::::::

Special cases.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$. Then we have the following.

1. $\unique(\cons(a,\nil)) = \btrue$.
2. $\unique(\cons(a,\cons(b,\nil))) = \bnot(\beq(a,b))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \unique(\cons(a,\nil)) \\
 & = & \band(\bnot(\elt(a,\nil)),\unique(\nil)) \\
 & = & \band(\bnot(\bfalse),\btrue) \\
 &     \href{@not@#thm-not-false}
   = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \unique(\cons(a,\cons(b,\nil))) \\
 & = & \band(\bnot(\elt(a,\cons(b,\nil))),\unique(\cons(b,\nil))) \\
 & = & \band(\bnot(\beq(a,b)),\btrue) \\
 &     \href{@and@#thm-and-true-right}
   = & \bnot(\beq(a,b))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_single :: (List t, Equal a)
>   => t a -> Test (a -> Bool)
> _test_unique_single t =
>   testName "unique(cons(a,nil)) == true" $
>     \a -> unique (cons a (nil `withTypeOf` t))
> 
> 
> _test_unique_double :: (List t, Equal a)
>   => t a -> Test (a -> a -> Bool)
> _test_unique_double t =
>   testName "unique(cons(a,cons(b,nil))) == not(eq(a,b))" $
>     \a b -> eq 
>       (unique (cons a (cons b (nil `withTypeOf` t))))
>       (not (eq a b))

::::::::::::::::::::
::::::::::::::::::::

$\unique$ is "down closed" with respect to $\sublist$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$ and $\unique(y) = \btrue$, then $\unique(x) = \btrue$.

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, suppose $\sublist(x,y) = \btrue$. Then we have $x = \nil$, and thus $\unique(x) = \btrue$. For the inductive step, suppose the implication holds for all $x$ for some $y$ and let $b \in A$. Suppose further that $\unique(\cons(b,y)) = \btrue$ and $\sublist(x,\cons(b,y)) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, then $\unique(x) = \btrue$ as needed. Suppose instead that $x = \cons(a,u)$ for some $a \in A$ and $u \in \lists{A}$. Note first that since $\unique(\cons(b,y)) = \btrue$, we have $$\band(\bnot(\elt(a,x)),\unique(y)) = \btrue;$$ in particular, $\unique(y) = \btrue$.  We now consider two possibilities. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(\cons(a,u),y) \\
 & = & \sublist(x,y).
\end{eqnarray*}$$
By the inductive hypothesis we have $\unique(x) = \btrue$ as needed. Suppose instead that $a = b$. Note that $\bnot(\elt(a,y))$, so $\bnot(\elt(a,u))$. Now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y).
\end{eqnarray*}$$
Again by the inductive hypothesis we have $\unique(u) = \btrue$. So
$$\begin{eqnarray*}
 &   & \unique(x) \\
 & = & \unique(\cons(a,u)) \\
 & = & \band(\bnot(\elt(a,u)),\unique(u)) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_sublist :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> Bool)
> _test_unique_sublist _ =
>   testName "if and(unique(x),sublist(y,x)) then unique(y)" $
>    \x y -> if and (unique x) (sublist y x)
>      then unique y
>      else true

::::::::::::::::::::
::::::::::::::::::::

If $f$ is injective, $\map(f)$ preserves uniqueness.

:::::: theorem :::::
Let $A$ and $B$ be sets with $x \in \lists{A}$ and $f : A \rightarrow B$. If $f$ is injective then $\unique(x) = \unique(\map(f)(x))$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \unique(\map(f)(x)) \\
 & = & \unique(\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \unique(\nil) \\
 & = & \unique(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $f$ for some $x$ and let $a \in A$. Suppose further that $\unique(\cons(a,x)) = \btrue$. Now if $f$ is injective, we have $\elt(f(a),\map(f)(x)) = \elt(a,x)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \unique(\map(f)(\cons(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \unique(\cons(f(a),\map(f)(x))) \\
 & = & \band(\bnot(\elt(f(a),\map(f)(x))),\unique(\map(f)(x))) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

$\unique$ and $\filter$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $p : A \rightarrow \bool$. If $\unique(x) = \btrue$, then $\unique(\filter(p,x)) = \btrue$.

::: proof ::::::::::
Note that $\sublist(\filter(p,x),x) = \btrue$; so we have $\unique(\filter(p,x)) = \btrue$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_filter :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_unique_filter _ =
>   testName "if unique(x) then unique(filter(p)(x))" $
>    \p x -> if unique x
>      then unique (filter p x)
>      else true

::::::::::::::::::::
::::::::::::::::::::

$\unique$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then $$\unique(\snoc(a,x)) = \band(\bnot(\elt(a,x)),\unique(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \unique(\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \unique(\cons(a,\nil)) \\
 & = & \band(\bnot(\elt(a,\nil)),\unique(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$ and let $b \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \unique(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \unique(\cons(b,\snoc(a,x))) \\
 & = & \band(\bnot(\elt(b,\snoc(a,x))),\unique(\snoc(a,x))) \\
 & = & \band(\bnot(\bif{\beq(b,a)}{\btrue}{\elt(b,x)}),\unique(\snoc(a,x))) \\
 & = & \band(\bnot(\elt(b,\cons(a,x))),\band(\bnot(\elt(a,x))),\unique(x)) \\
 & = & \band(\bnot(\bif{\beq(b,a)}{\btrue}{\elt(b,x)}),\band(\bnot(\elt(a,x)),\unique(x))) \\
 & = & \band(\bif{\beq(b,a)}{\bfalse}{\bnot(\elt(b,x))},\band(\bnot(\elt(a,x)),\unique(x))) \\
 & = & \bif{\beq(a,b)}{\band(\bfalse,\band(\bnot(\elt(a,x)),\unique(x)))}{\band(\bnot(\elt(b,x)),\band(\bnot(\elt(a,x)),\unique(x)))} \\
 & = & \bif{\beq(a,b)}{\bfalse}{\band(\band(\bnot(\elt(b,x)),\bnot(\elt(a,x))),\unique(x))} \\
 &     \href{@and@#thm-and-commutative}
   = & \bif{\beq(a,b)}{\bfalse}{\band(\band(\bnot(\elt(a,x)),\bnot(\elt(b,x))),\unique(x))} \\
 &     \href{@and@#thm-and-associative}
   = & \bif{\beq(a,b)}{\bfalse}{\band(\bnot(\elt(a,x)),\band(\bnot(\elt(b,x)),\unique(x)))} \\
 &     \href{@and@#thm-and-false-left}
   = & \bif{\beq(a,b)}{\band(\bfalse,\band(\bnot(\elt(b,x)),\unique(x)))}{\band(\bnot(\elt(a,x)),\band(\bnot(\elt(b,x)),\unique(x)))} \\
 & = & \band(\bif{\beq(a,b)}{\bfalse}{\bnot(\elt(a,x))},\band(\bnot(\elt(b,x)),\unique(x))) \\
 & = & \band(\bnot(\bif{\beq(a,b)}{\btrue}{\elt(a,x)}),\band(\bnot(\elt(b,x)),\unique(x))) \\
 & = & \band(\bnot(\elt(a,\cons(b,x))),\band(\bnot(\elt(b,x)),\unique(x))) \\
 & = & \band(\bnot(\elt(a,\cons(b,x))),\unique(\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_snoc :: (List t, Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_unique_snoc _ =
>   testName "unique(snoc(a,x)) == and(not(elt(a,x)),unique(x))" $
>    \a x -> eq (unique (snoc a x)) (and (not (elt a x)) (unique x))

::::::::::::::::::::
::::::::::::::::::::

$\unique$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$. Then $\unique(x) = \unique(\rev(x))$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \unique(\rev(x)) \\
 & = & \unique(\rev(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \unique(\nil) \\
 & = & \unique(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \unique(\rev(\cons(a,x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \unique(\snoc(a,\rev(x))) \\
 & = & \band(\bnot(\elt(a,\rev(x))),\unique(\rev(x))) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_rev :: (List t, Equal a)
>   => t a -> Test (t a -> Bool)
> _test_unique_rev _ =
>   testName "unique(x) == unique(rev(x))" $
>   \x -> eq (unique x) (unique (rev x))

::::::::::::::::::::
::::::::::::::::::::

$\range$s are unique.

:::::: theorem :::::
Let $a,b \in \nats$. We have $$\unique(\range(a,b)) = \btrue.$$

::: proof ::::::::::
We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \unique(\range(a,\zero)) \\
 & = & \unique(\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $b$. Now
$$\begin{eqnarray*}
 &   & \unique(a,\next(b)) \\
 & = & \unique(\cons(a,\range(\next(a),b))) \\
 & = & \band(\bnot(\elt(a,\range(\next(a),b))),\unique(\range(\next(a),b))) \\
 & = & \band(\bnot(\elt(a,\range(\next(a),b))),\btrue) \\
 &     \href{@and@#thm-and-true-right}
   = & \bnot(\elt(a,\range(\next(a),b))) \\
 & = & \bnot(\bfalse) \\
 &     \href{@not@#thm-not-false}
   = & \btrue
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_unique_range :: (List t, Natural n, Equal n)
>   => t a -> n -> Test (t n -> n -> n -> Bool)
> _test_unique_range _ n =
>   testName "unique(range(a,b)) == true" $
>   \t a b -> unique ((range a b) `withTypeOf` t)

::::::::::::::::::::
::::::::::::::::::::

$\unique$ can detect $\elt$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in X$, we have $$\all(\unique)(\map(\cons(a,\cons(-,\nil)))(x)) = \bnot(\elt(a,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\unique)(\map(\cons(a,\cons(-,x)))(\nil)) \\
 & = & \all(\unique)(\nil) \\
 & = & \btrue \\
 &     \href{@not@#thm-not-false}
   = & \bnot(\bfalse) \\
 & = & \bnot(\elt(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \all(\unique)(\map(\cons(a,\cons(-,\nil)))(\cons(b,x))) \\
 & = & \all(\unique)(\cons(\cons(a,\cons(b,\nil)),\map(\cons(a,\cons(-,\nil)))(x))) \\
 & = & \band(\unique(\cons(a,\cons(b,\nil))),\all(\unique)(\map(\cons(a,\cons(-,\nil)))(x))) \\
 & = & \band(\unique(\cons(a,\cons(b,\nil))),\bnot(\elt(a,x))) \\
 & = & \band(\bnot(\beq(a,b)),\bnot(\elt(a,x))) \\
 &     \href{@or@#thm-demorgan-not-or}
   = & \bnot(\bor(\beq(a,b),\elt(a,x))) \\
 & = & \bnot(\elt(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_elt :: (List t, Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_unique_elt t =
>   testName "all(unique)(map(cons(a,cons(-,nil)))(x)) == not(elt(a,x))" $
>   \a x -> eq
>     (all unique (map (\b -> cons a (cons b (nil `withTypeOf` t))) x))
>     (not (elt a x))

::::::::::::::::::::
::::::::::::::::::::

$\unique$ and $\select$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\unique(x) = \all(\unique)(\select(\next(\next(\zero)),x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\unique)(\select(\next(\next(\zero)),x)) \\
 & = & \all(\unique)(\select(\next(\next(\zero)),\nil)) \\
 & = & \all(\unique)(\nil) \\
 & = & \btrue \\
 & = & \unique(\nil) \\
 & = & \unique(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \all(\unique)(\select(\next(\next(\zero)),\cons(a,x))) \\
 & = & \all(\unique)(\cat(\map(\cons(a,-))(\select(\next(\zero),x)),\select(\next(\next(\zero)),x))) \\
 & = & \all(\unique)(\cat(\map(\cons(a,-))(\map(\cons(-,\nil))(x)),\select(\next(\next(\zero)),x))) \\
 & = & \all(\unique)(\cat(\map(\cons(a,\cons(-,\nil)))(x),\select(\next(\next(\zero)),x))) \\
 & = & \band(\all(\unique)(\map(\cons(a,\cons(-,\nil)))(x)),\all(\unique)(\select(\next(\next(\zero)),x))) \\
 & = & \band(\all(\unique)(\map(\cons(a,\cons(-,\nil)))(x)),\unique(x)) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unique_select_two :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (t a -> Bool)
> _test_unique_select_two _ n =
>   testName "unique(x) == unique(select(next(next(zero)),x))" $
>   \x -> eq
>     (unique x)
>     (all unique (select (next (next zero) `withTypeOf` n) x))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_unique ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Arbitrary (t n), Show (t n), Equal (t n)
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_unique t n maxSize numCases = do
>   testLabel1 "unique" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_unique_nil t)
>   runTest args (_test_unique_cons t)
>   runTest args (_test_unique_single t)
>   runTest args (_test_unique_double t)
>   runTest args (_test_unique_sublist t)
>   runTest args (_test_unique_filter t)
>   runTest args (_test_unique_snoc t)
>   runTest args (_test_unique_rev t)
>   runTest args (_test_unique_range t n)
>   runTest args (_test_unique_elt t)
>   runTest args (_test_unique_select_two t n)

Main:

> main_unique :: IO ()
> main_unique = do
>   _test_unique (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_unique (nil :: ConsList Unary) (zero :: Unary) 20 100
