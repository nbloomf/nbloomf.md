---
title: Coprime To
author: nbloomf
date: 2017-04-11
tags: arithmetic-made-difficult, literate-haskell
slug: coprime
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module CoprimeTo
>   ( coprime, _test_coprime, main_coprime
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> import GreatestCommonDivisor

Today we'll take a break from reasoning about $\ngcd$ to name a special relationship among natural numbers: *coprimality*. Recall that two integers are called *coprime* if their greatest common divisor is 1. This definition does not require recursion.

:::::: definition ::
We define $\ncoprime : \nats \times \nats \rightarrow \bool$ by $$\ncoprime(a,b) = \beq(\ngcd(a,b),\next(\zero)).$$

In Haskell:

> coprime :: (Natural n, Equal n) => n -> n -> Bool
> coprime a b = eq (next zero) (gcd a b)

::::::::::::::::::::

Simple though it is, coprimality has some nice properties. We only need these two for now. The first result is known as Euclid's Lemma.

:::::: theorem :::::
Let $a,b,c \in \nats$ such that $\ncoprime(a,b)$ and $\ndiv(a,\ntimes(b,c))$. Then $\ndiv(a,c)$.

::: proof ::::::::::
Since $\next(\zero) = \ngcd(a,b)$, we have
$$\begin{eqnarray*}
 &   & c \\
 &     \href{@times@#thm-times-one-left}
   = & \ntimes(\next(\zero),c) \\
 & = & \ntimes(\ngcd(a,b),c) \\
 & = & \ngcd(\ntimes(a,c),\ntimes(b,c)).
\end{eqnarray*}$$
But now $\ndiv(a,\ntimes(a,c))$ and $\ndiv(a,\ntimes(b,c))$, so that $\ndiv(a,c)$ by the universal property of $\ngcd$.
::::::::::::::::::::

::: test :::::::::::

> _test_coprime_euclids_lemma :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_coprime_euclids_lemma _ =
>   testName "if coprime(a,b) and div(a,times(b,c)) then div(a,c)" $
>   \a b c -> if and (coprime a b) (div a (times b c))
>     then div a c
>     else true

::::::::::::::::::::
::::::::::::::::::::

The second result doesn't have a name as far as I know, but is still handy. The quotients of nonzero $a$ and $b$ by their (nonzero) greatest common divisor are coprime.

:::::: theorem :::::
Let $a,b,u,v \in \nats$ such that $a,b \neq \zero$, $$a = \ntimes(u,\ngcd(a,b))$$ and $$b = \ntimes(v,\ngcd(a,b)).$$ Then $\ncoprime(u,v)$.

::: proof ::::::::::
Let $k = \ngcd(u,v)$, and say $u = \ntimes(s,k)$ and $v = \ntimes(t,k)$. Now
$$\begin{eqnarray*}
 &   & a \\
 & = & \ntimes(u,\ngcd(a,b)) \\
 & = & \ntimes(s,\ntimes(k,\ngcd(a,b)))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & b \\
 & = & \ntimes(v,\ngcd(a,b)) \\
 & = & \ntimes(t,\ntimes(k,\ngcd(a,b))).
\end{eqnarray*}$$
In particular, $\ntimes(k,\ngcd(a,b))$ is a common divisor of $a$ and $b$, and thus we have $$\ndiv(\ntimes(k,\ngcd(a,b)),\ngcd(a,b)).$$ Note that $\ngcd(a,b) \neq \zero$, so we have $\ndiv(k,\next(\zero))$. Thus $k = \next(\zero)$, and we have $\ncoprime(u,v)$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_coprime_gcd_quo :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_coprime_gcd_quo _ =
>   testName "coprime(quo(next(a),gcd(next(a),next(b))),quo(next(b),gcd(next(a),next(b))))" $
>   \x y -> let
>     a = next x
>     b = next y
>     u = quo a (gcd a b)
>     v = quo b (gcd a b)
>   in eq (coprime u v) true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_coprime ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_coprime n maxSize numCases = do
>   testLabel1 "coprime" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_coprime_euclids_lemma n)
>   runTest args (_test_coprime_gcd_quo n)

Main:

> main_coprime :: IO ()
> main_coprime = do
>   _test_coprime (zero :: Unary) 20 100
