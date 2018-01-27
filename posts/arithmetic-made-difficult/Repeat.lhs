---
title: Repeat
author: nbloomf
date: 2017-05-22
tags: arithmetic-made-difficult, literate-haskell
slug: repeat
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Repeat
>   ( repeat, _test_repeat, main_repeat
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import DisjointUnions
> import NaturalNumbers
> import Plus
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count

So far we've defined a bunch of functions that operate on lists, but still only one that can create one out of nothing, namely $\range$. ($\tails$ and $\inits$ create lists, but only if we have one to start with.) Today we'll nail down another list-creating utility, $\repeat$.

:::::: definition ::
Let $A$ be a set, and define $f : A \rightarrow 1 + A \times A$ by $f(x) = \rgt((x,x))$. Now define $\repeat : \nats \rightarrow {\lists{A}}^A$ by $$\repeat(n)(a) = \unfoldN(f)(n,a).$$

In Haskell:

> repeat :: (List t, Natural n) => n -> a -> t a
> repeat n a = unfoldN f n a
>   where
>     f x = rgt (x,x)

::::::::::::::::::::

Since $\repeat$ is defined as an unfoldN, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\repeat$ is the unique map $f : \nats \rightarrow {\lists{A}}^A$ satisfying the following equations for all $n \in \nats$ and $a \in A$.
$$\left\{\begin{array}{l}
 f(\zero)(a) = \nil \\
 f(\next(n))(a) = \cons(a,f(n)(a))
\end{array}\right.$$

::: test :::::::::::

> _test_repeat_zero :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (a -> Bool)
> _test_repeat_zero t k =
>   testName "repeat(zero,a) == nil" $
>   \a -> eq
>     (repeat (zero `withTypeOf` k) a)
>     (nil `withTypeOf` t)
> 
> 
> _test_repeat_next :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> Bool)
> _test_repeat_next t _ =
>   testName "repeat(next(n),a) == cons(a,repeat(n,a))" $
>   \n a -> eq
>     (repeat (next n) a)
>     ((cons a (repeat n a)) `withTypeOf` t)

::::::::::::::::::::
::::::::::::::::::::

$\repeat$ is kind of boring. I'm not sure if we'll actually need these, but here are some interactions using $\repeat$.

$\repeat$ and $\length$.

:::::: theorem :::::
Let $A$ be a set. For all $n \in \nats$ and $a \in A$ we have $$\length(\repeat(n,a)) = n.$$

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \length(\repeat(\zero,a)) \\
 & = & \length(\nil) \\
 & = & \zero
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $n$. Then we have
$$\begin{eqnarray*}
 &   & \length(\repeat(\next(n),a)) \\
 & = & \length(\cons(a,\repeat(n,a))) \\
 & = & \next(\length(\repeat(n,a))) \\
 & = & \next(n)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_repeat_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> Bool)
> _test_repeat_length t _ =
>  testName "length(repeat(n,a)) == n" $
>  \n a -> eq (length (repeat n a `withTypeOf` t)) n

::::::::::::::::::::
::::::::::::::::::::

$\repeat$ and $\map$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $n \in \nats$ and $a \in A$, we have $$\map(f)(\repeat(n,a)) = \repeat(n,f(a)).$$

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \map(f)(\repeat(\zero,a)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \repeat(\zero,f(a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now we have
$$\begin{eqnarray*}
 &   & \map(f)(\repeat(\next(n),a)) \\
 & = & \map(f)(\cons(a,\repeat(n,a))) \\
 & = & \cons(f(a),\map(f)(\repeat(n,a))) \\
 & = & \cons(f(a),\repeat(n,f(a))) \\
 & = & \repeat(\next(n),f(a))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_repeat_map :: (List t, Equal a, Equal b, Natural n, Equal n, Equal (t b))
>   => t a -> t b -> n -> Test ((a -> b) -> n -> a -> Bool)
> _test_repeat_map t _ _ =
>   testName "map(f)(repeat(n,a)) == repeat(n,f(a))" $
>   \f k a -> eq
>     (repeat k (f a))
>     (map f (repeat k a `withTypeOf` t))

::::::::::::::::::::
::::::::::::::::::::

$\repeat$ and $\nplus$.

:::::: theorem :::::
Let $A$ be a set. For all $m,n \in \nats$ and $a \in A$, we have $$\repeat(\nplus(m,n),a) = \cat(\repeat(m,a),\repeat(n,a)).$$

::: proof ::::::::::
We proceed by induction on $m$. For the base case $m = \zero$, we have
$$\begin{eqnarray*}
 &   & \repeat(\nplus(\zero,n),a) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \repeat(n,a) \\
 & = & \cat(\nil,\repeat(n,a)) \\
 & = & \cat(\repeat(\zero,a),\repeat(n,a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $m$. Now we have
$$\begin{eqnarray*}
 &   & \repeat(\nplus(\next(m),n),a) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \repeat(\next(\nplus(m,n)),a) \\
 & = & \cons(a,\repeat(\nplus(m,n),a)) \\
 & = & \cons(a,\cat(\repeat(m,a),\repeat(n,a))) \\
 & = & \cat(\cons(a,\repeat(m,a)),\repeat(n,a)) \\
 & = & \cat(\repeat(\next(m),a),\repeat(n,a))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_repeat_plus :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> n -> a -> Bool)
> _test_repeat_plus t _ =
>   testName "repeat(plus(m,n),a) == cat(repeat(m,a),repeat(n,a))" $
>   \m n a -> eq
>     ((repeat (plus m n) a) `withTypeOf` t)
>     (cat (repeat m a) (repeat n a))

::::::::::::::::::::
::::::::::::::::::::

$\repeat$ and $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $n \in \nats$ and $a \in A$, we have $$\snoc(a,\repeat(n,a)) = \repeat(\next(n),a).$$

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \snoc(a,\repeat(\zero)(a)) \\
 & = & \snoc(a,\nil) \\
 & = & \cons(a,\nil) \\
 & = & \cons(a,\repeat(\zero)(a)) \\
 & = & \repeat(\next(n))(a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now we have
$$\begin{eqnarray*}
 &   & \snoc(a,\repeat(\next(n))(a)) \\
 & = & \snoc(a,\cons(a,\repeat(n)(a))) \\
 & = & \cons(a,\snoc(a,\repeat(n)(a))) \\
 & = & \cons(a,\repeat(\next(n))(a)) \\
 & = & \repeat(\next(\next(n)))(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_repeat_snoc :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> Bool)
> _test_repeat_snoc t _ =
>   testName "snoc(a,repeat(n)(a)) == repeat(next(n))(a)" $
>   \n a -> eq
>     (snoc a ((repeat n a) `withTypeOf` t))
>     (repeat (next n) a)

::::::::::::::::::::
::::::::::::::::::::

$\repeat$ and $\rev$.

:::::: theorem :::::
Let $A$ be a set. For all $n \in \nats$ and $a \in A$, we have $$\rev(\repeat(n,a)) = \repeat(n,a).$$

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \rev(\repeat(\zero,a)) \\
 & = & \rev(\nil) \\
 & = & \nil \\
 & = & \repeat(\zero,a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Then we have
$$\begin{eqnarray*}
 &   & \rev(\repeat(\next(n),a)) \\
 & = & \rev(\cons(a,\repeat(n,a))) \\
 & = & \snoc(a,\rev(\repeat(n,a))) \\
 & = & \snoc(a,\repeat(n,a)) \\
 & = & \repeat(\next(n),a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_repeat_rev :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> Bool)
> _test_repeat_rev t _ =
>   testName "rev(repeat(n,a)) == repeat(n,a)" $
>   \n a -> eq
>     (rev (repeat n a))
>     (repeat n a `withTypeOf` t)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_repeat ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName b, Equal b, Show b, Arbitrary b, CoArbitrary b
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Arbitrary n, Show n, Equal n
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a)), Equal (t b)
>   ) => t a -> t b -> n -> Int -> Int -> IO ()
> _test_repeat t u n maxSize numCases = do
>   testLabel2 "repeat" t n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_repeat_zero t n)
>   runTest args (_test_repeat_next t n)
>   runTest args (_test_repeat_length t n)
>   runTest args (_test_repeat_map t u n)
>   runTest args (_test_repeat_plus t n)
>   runTest args (_test_repeat_snoc t n)
>   runTest args (_test_repeat_rev t n)

Main:

> main_repeat :: IO ()
> main_repeat = do
>   _test_repeat (nil :: ConsList Bool)  (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_repeat (nil :: ConsList Unary) (nil :: ConsList Unary) (zero :: Unary) 20 100
