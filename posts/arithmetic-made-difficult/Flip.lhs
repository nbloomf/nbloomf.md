---
title: Flip
author: nbloomf
date: 2018-02-17
tags: arithmetic-made-difficult, literate-haskell
slug: flip
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Flip (
>   flip, _test_flip, main_flip
> ) where
> 
> import Testing
> import Functions

It turns out that equational proofs are much simpler to state and verify if we define new functions in the so-called _pointfree_ style. A pointfree function definition is one that does not refer to its arguments explicitly; for example, suppose we have two functions $f : A \rightarrow B$ and $g : B \rightarrow C$, and have defined a new function $h : A \rightarrow C$ by $$h(x) = g(f(x)).$$ Of course this definition is equivalent to $$h(x) = \compose(g)(f)(x).$$ But now the rightmost argument, $x$, can be omitted, leaving $$h = \compose(g)(f).$$ This final statement is written in the pointfree style. We'll see later that definitions will cooperate better with equational reasoning if they are in pointfree form. To make this work, we'll need a stable of operators for manipulating functions, like $\compose$ in the above example. In all cases the goal will be to move function arguments around; for instance, $\compose$ lets us move a rightmost argument "up" one level of parentheses.

In this post we'll define a family of operators that rearrange the arguments of a multi-argument function. The first example is $\flip$, which flips the arguments of a two-argument function.

:::::: definition ::
[]{#def-flip}
Let $A$, $B$, and $C$ be sets. Given $f : A \rightarrow C^B$, we define $\flip(f) : B \rightarrow C^A$ by $$\flip(f)(b)(a) = f(a)(b).$$

In Haskell:

> flip :: (a -> b -> c) -> b -> a -> c
> flip f b a = f a b

::::::::::::::::::::

$\flip$ is an involution.

:::::: theorem :::::
[]{#thm-flip-involution}
Let $A$, $B$, and $C$ be sets. For all $f : A \rightarrow C^B$, we have $$\flip(\flip(f)) = f.$$

::: proof ::::::::::
Let $a \in A$ and $b \in B$. Then we have
$$\begin{eqnarray*}
 &   & \flip(\flip(f))(a)(b) \\
 &     \href{@functions@#def-flip}
   = & \flip(f)(b)(a) \\
 &     \href{@functions@#def-flip}
   = & f(a)(b)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip_involution :: (Equal c)
>   => a -> b -> c -> Test ((a -> b -> c) -> a -> b -> Bool)
> _test_flip_involution _ _ _ =
>   testName "flip(flip(f)) == f" $
>   \f a b -> eq (flip (flip f) a b) (f a b)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_flip ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b
>   , Equal c, Show c, Arbitrary c, CoArbitrary c
>   , Equal d, Show d, Arbitrary d, CoArbitrary d
>   ) => a -> b -> c -> d -> Int -> Int -> IO ()
> _test_flip a b c d size cases = do
>   testLabel0 "flip"
>   let args = testArgs size cases
> 
>   runTest args (_test_flip_involution a b c)

Main:

> main_flip :: IO ()
> main_flip = do
>   _test_flip () () () () 1 1
