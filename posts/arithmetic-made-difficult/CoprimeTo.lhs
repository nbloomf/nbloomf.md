---
title: Coprime To
author: nbloomf
date: 2017-04-11
tags: arithmetic-made-difficult, literate-haskell
---

> module CoprimeTo
>   ( coprime, _test_coprime
>   ) where
>
> import Prelude hiding (div, rem, gcd, lcm)
>
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> import GreatestCommonDivisor
> 
> import Test.QuickCheck

Today we'll take a break from reasoning about $\ngcd$ to name a special relationship among natural numbers: *coprimality*. Recall that two integers are called *coprime* if their greatest common divisor is 1. This definition does not require recursion.

<div class="result">
<div class="defn"><p>
We define $\ncoprime : \nats \times \nats \rightarrow \bool$ by $$\ncoprime(a,b) = \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ \ngcd(a,b) = \next(\zero) \\ \bfalse & \mathrm{otherwise}. \end{array}\right.$$
</p></div>
</div>

Simple though it is, coprimality has some nice properties. We only need these two for now. The first result is known as Euclid's Lemma.

<div class="result">
<div class="thm"><p>
Let $a,b,c \in \nats$ such that $\ncoprime(a,b)$ and $\ndiv(a,\ntimes(b,c))$. Then $\ndiv(a,c)$.
</p></div>

<div class="proof"><p>
Since $\next(\zero) = \ngcd(a,b)$, we have
$$\begin{eqnarray*}
 &   & c \\
 & = & \ntimes(\next(\zero),c) \\
 & = & \ntimes(\ngcd(a,b),c) \\
 & = & \ngcd(\ntimes(a,c),\ntimes(b,c)).
\end{eqnarray*}$$
But now $\ndiv(a,\ntimes(a,c))$ and $\ndiv(a,\ntimes(b,c))$, so that $\ndiv(a,c)$ by the universal property of $\ngcd$.
</p></div>
</div>

The second result doesn't have a name as far as I know, but is still handy. The quotients of nonzero $a$ and $b$ by their (nonzero) greatest common divisor are coprime.

<div class="result">
<div class="thm"><p>
Let $a,b,u,v \in \nats$ such that $a,b \neq \zero$, $$a = \ntimes(u,\ngcd(a,b))$$ and $$b = \ntimes(v,\ngcd(a,b)).$$ Then $\ncoprime(u,v)$.
</p></div>

<div class="proof"><p>
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
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``coprime``:

> coprime :: (Natural t) => t -> t -> Bool
> coprime a b = (next zero) == (gcd a b)

Property tests:

> _test_coprime_gcd_quo :: (Natural t) => t -> t -> t -> Bool
> _test_coprime_gcd_quo _ x y =
>   let
>     a = next x
>     b = next y
>     u = quo a (gcd a b)
>     v = quo b (gcd a b)
>   in coprime u v

And the suite:

> -- run all tests for coprime
> _test_coprime :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_coprime t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_coprime_gcd_quo t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
