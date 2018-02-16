---
title: Range
author: nbloomf
date: 2017-05-05
tags: arithmetic-made-difficult, literate-haskell
slug: range
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Range
>   ( range, _test_range, main_range
>   ) where
> 
> import Testing
> import Tuples
> import DisjointUnions
> import Booleans
> import Not
> import And
> import Or
> import NaturalNumbers
> import Plus
> import Lists
> import Snoc
> import Reverse
> import Cat
> import Length
> import At
> import Map
> import UnfoldN

For our first application of $\unfoldN{\ast}$ we'll define a function, $\range$, that constructs lists of natural numbers. There are a few ways to do this. We could take an argument $n$ and construct the list of natural numbers from $\zero$ to $n$, but this is too specialized. We could instead take *two* arguments $a$ and $b$ and construct the list of natural numbers from $a$ to $b$, but we'll have to check whether or not the arguments are in order. A third option -- and the one we'll take -- is to take two arguments $a$ and $b$, and construct the list of the first $b$ natural numbers starting from $a$.

:::::: definition ::
Define $f : \nats \rightarrow \ast + \nats \times \nats$ by $$f(k) = (\next(k),k).$$ We then define $\range : \nats \times \nats \rightarrow \lists{\nats}$ by $$\range(a,b) = \unfoldN(f,b,a).$$

In Haskell:

> range :: (List t, Natural n, Equal n) => n -> n -> t n
> range a b = unfoldN f b a
>   where f k = rgt (tup (next k) k)

::::::::::::::::::::

Since $\range$ is an $\unfoldN{\ast}$, it is the unique solution to a system of functional equations.

:::::: corollary :::
$\range$ is the unique $f : \nats \times \nats \rightarrow \lists{\nats}$ satisfying the following system of equations for all $a,b \in \nats$.
$$\left\{\begin{array}{l}
 f(a,\zero) = \nil \\
 f(a,\next(b)) = \cons(a,f(\next(a),b))
\end{array}\right.$$

::: test :::::::::::

> _test_range_zero :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> Bool)
> _test_range_zero t =
>   testName "range(a,zero) == nil" $
>   \a -> eq (range a zero) (nil `withTypeOf` t)
> 
> 
> _test_range_next :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_next t =
>   testName "range(a,next(b)) == cons(a,range(next(a),b))" $
>   \a b -> eq
>     ((range a (next b)) `withTypeOf` t)
>     (cons a (range (next a) b))

::::::::::::::::::::
::::::::::::::::::::

A special case.

:::::: theorem :::::
For all $a \in \nats$ we have $\range(a,\next(\zero)) = \cons(a,\nil)$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \range(a,\next(\zero)) \\
 & = & \cons(a,\range(\next(a),\zero)) \\
 & = & \cons(a,\nil)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_one :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> Bool)
> _test_range_one t =
>   testName "range(a,next(zero)) == cons(a,nil)" $
>   \a -> eq (range a (next zero)) ((cons a nil) `withTypeOf` t)

::::::::::::::::::::
::::::::::::::::::::

The $\length$ of a $\range$ is predictable.

:::::: theorem :::::
For all $a,b \in \nats$, we have $\length(\range(a,b)) = b$.

::: proof ::::::::::
We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\range(a,b)) \\
 & = & \length(\range(a,\zero)) \\
 & = & \length(\nil) \\
 &     \href{@length@#cor-length-nil}
   = & \zero \\
 & = & b
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $b$. Now
$$\begin{eqnarray*}
 &   & \length(\range(a,\next(b))) \\
 & = & \length(\cons(a,\range(\next(a),b))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\range(\next(a),b))) \\
 & = & \next(b)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_length :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_length t =
>   testName "length(range(a,b)) == b" $
>   \a b -> eq (length ((range a b) `withTypeOf` t)) b

::::::::::::::::::::
::::::::::::::::::::

$\range$ interacts with $\snoc$.

:::::: theorem :::::
For all $a,b \in \nats$ we have $$\range(a,\next(b)) = \snoc(\nplus(a,b),\range(a,b)).$$

::: proof ::::::::::
We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(a,\next(b)) \\
 & = & \range(a,\next(\zero)) \\
 & = & \cons(a,\nil) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \snoc(a,\nil) \\
 & = & \snoc(\nplus(a,\zero),\range(a,\zero)) \\
 & = & \snoc(\nplus(a,b),\range(a,b))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $b$. Then we have
$$\begin{eqnarray*}
 &   & \range(a,\next(\next(b))) \\
 & = & \cons(a,\range(\next(a),\next(b))) \\
 & = & \cons(a,\snoc(\nplus(\next(a),b),\range(\next(a),b))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(\nplus(\next(a),b),\cons(a,\range(\next(a),b))) \\
 & = & \snoc(\nplus(a,\next(b)),\range(a,\next(b)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_snoc :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_snoc t =
>   testName "range(a,next(b)) == snoc(plus(a,b),range(a,b))" $
>   \a b -> eq
>     ((range a (next b)) `withTypeOf` t)
>     (snoc (plus a b) (range a b))

::::::::::::::::::::
::::::::::::::::::::

$\range$ interacts with $\nplus$ in its second argument.

:::::: theorem :::::
If $a,b,c \in \nats$, we have $$\range(a,\nplus(b,c)) = \cat(\range(a,b),\range(\nplus(a,b),c)).$$

::: proof ::::::::::
We proceed by induction on $c$. For the base case $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(a,\nplus(b,c)) \\
 & = & \range(a,\nplus(b,\zero)) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & \range(a,b) \\
 & = & \cat(\range(a,b),\nil) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),\zero)) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),c))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $c$. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \range(a,\nplus(b,\next(c))) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \range(a,\next(\nplus(b,c))) \\
 & = & \snoc(\nplus(a,\nplus(b,c)),\range(a,\nplus(b,c))) \\
 & = & \snoc(\nplus(a,\nplus(b,c)),\cat(\range(a,b),\range(\nplus(a,b),c))) \\
 &     \href{@plus@#thm-plus-associative}
   = & \snoc(\nplus(\nplus(a,b),c),\cat(\range(a,b),\range(\nplus(a,b),c))) \\
 & = & \cat(\range(a,b),\snoc(\nplus(\nplus(a,b),c),\range(\nplus(a,b),c))) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),\next(c)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_plus_right :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> n -> Bool)
> _test_range_plus_right t =
>   testName "range(a,plus(b,c)) == cat(range(a,b),range(plus(a,b),c))" $
>   \a b c -> eq
>     ((range a (plus b c)) `withTypeOf` t)
>     (cat (range a b) (range (plus a b) c))

::::::::::::::::::::
::::::::::::::::::::

$\range$ interacts with $\next$ in its first argument.

:::::: theorem :::::
For all $a,b \in \nats$ we have $$\range(\next(a),b) = \map(\next)(\range(a,b)).$$

::: proof ::::::::::
We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(\next(a),b) \\
 & = & \range(\next(a),\zero) \\
 & = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\next)(\nil) \\
 & = & \map(\next)(\range(a,\zero)) \\
 & = & \map(\next)(\range(a,b))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $b$. Now
$$\begin{eqnarray*}
 &   & \range(\next(a),\next(b)) \\
 & = & \cons(\next(a),\range(\next(\next(a)),b)) \\
 & = & \cons(\next(a),\map(\next)(\range(\next(a),b))) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\next)(\cons(a,\range(\next(a),b))) \\
 & = & \map(\next)(\range(a,\next(b)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_next_left :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_next_left t =
>   testName "range(next(a),b) == map(next,range(a,b))" $
>   \a b -> eq
>     ((range (next a) b) `withTypeOf` t)
>     (map next (range a b))

::::::::::::::::::::
::::::::::::::::::::

And $\range$ interacts with $\nplus$ in its first argument. In this theorem we use a bit of new notation. When a function argument is replaced by a dash, we implicitly mean lambda-abstraction. That is, if $f$ is a function, then $f(-)$ is short for $\lambda x. f(x)$.

:::::: theorem :::::
If $a,b,c \in \nats$, we have $$\range(\nplus(a,b),c) = \map(\nplus(a,-))(\range(b,c)).$$

::: proof ::::::::::
We proceed by induction on $a$. For the base case $a = \zero$ note that $\nplus(a,-) = \id$, since for all $b \in \nats$ we have $$\nplus(\zero,-)(b) = \nplus(\zero,b) = b.$$ Thus
$$\begin{eqnarray*}
 &   & \range(\nplus(a,b),c) \\
 & = & \range(\nplus(\zero,b),c) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \range(b,c) \\
 & = & \map(\id)(\range(b,c)) \\
 & = & \map(\nplus(\zero,-))(\range(b,c)) \\
 & = & \map(\nplus(a,-))(\range(b,c))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $a$. Now
$$\begin{eqnarray*}
 &   & \range(\nplus(\next(a),b),c) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \range(\next(\nplus(a,b)),c) \\
 & = & \map(\next)(\range(\nplus(a,b),c)) \\
 & = & \map(\next)(\map(\nplus(a,-))(\range(b,c))) \\
 & = & (\map(\next) \circ \map(\nplus(a,-)))(\range(b,c)) \\
 & = & \map(\next(\nplus(a,-)))(\range(b,c)) \\
 & = & \map(\nplus(\next(a),-))(\range(b,c))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_range_plus_left :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> n -> Bool)
> _test_range_plus_left t =
>   testName "range(plus(a,b),c) == map(plus(a,-),range(b,c))" $
>   \a b c -> eq
>     ((range (plus a b) c) `withTypeOf` t)
>     (map (plus a) (range b c))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_range ::
>   ( TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t n), List t, Equal (t n), Show (t n), Arbitrary (t n)
>   ) => t n -> Int -> Int -> IO ()
> _test_range t maxSize numCases = do
>   testLabel1 "range" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_range_zero t)
>   runTest args (_test_range_next t)
>   runTest args (_test_range_one t)
>   runTest args (_test_range_length t)
>   runTest args (_test_range_snoc t)
>   runTest args (_test_range_plus_right t)
>   runTest args (_test_range_next_left t)
>   runTest args (_test_range_plus_left t)

Main:

> main_range :: IO ()
> main_range = do
>   _test_range (nil :: ConsList Unary) 20 100
