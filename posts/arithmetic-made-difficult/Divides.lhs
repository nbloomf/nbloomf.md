---
title: Divides
author: nbloomf
date: 2017-04-09
tags: arithmetic-made-difficult, literate-haskell
---

> module Divides
>   ( div, _test_div
>   ) where
>
> import Prelude hiding (div, rem)
>
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> import DivisionAlgorithm
> 
> import Test.QuickCheck

With the division algorithm in hand we can define what it means for one natural number to divide another.

<div class="result">
<div class="defn"><p>
We define $\ndiv : \nats \times \nats \rightarrow \bool$ by $$\ndiv(a,b) = \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ \nrem(b,a) = \zero \\ \bfalse & \mathrm{otherwise}. \end{array}\right.$$
</p></div>
</div>

Now $\ndiv$ is to $\ntimes$ as $\nleq$ is to $\nplus$ as follows.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\ndiv(a,b) = \btrue$ if and only if there exists $c \in \nats$ such that $b = \ntimes(c,a)$.
</div>

<div class="proof"><p>
Suppose first that $\ndiv(a,b) = \btrue$. Letting $(q,r) = \ndivalg(b,a)$, we have $r = \zero$, so that $$b = \nplus(\ntimes(q,a),r) = \ntimes(q,a)$$ as claimed.

Suppose now that there is a natural number $c$ such that $b = \ntimes(c,a)$. If $a = \zero$, then in fact $b = \zero$, and we have $\nrem(b,a) = \zero$, so that $\ndiv(a,b)$. Suppose instead that $a = \next(d)$. Since $$b = \nplus(\ntimes(c,\next(d)),\zero)$$ and $$\nleq(\zero,\next(d)),$$ we have $$(c,\zero) = \ndivalg(b,a).$$ Thus $\nrem(b,a) = \zero$ as needed.
</p></div>
</div>

From here the usual properties of divisibility are straightforward.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. We have the following.

1. $\ndiv(a,\zero)$.
2. If $\ndiv(\zero,a)$, then $a = \zero$.
3. $\ndiv(\next(\zero),a)$.
4. $\ndiv(a,a)$.
5. If $\ndiv(a,b)$ and $\ndiv(b,a)$, then $a = b$.
6. If $\ndiv(a,b)$ and $\ndiv(b,c)$, then $\ndiv(a,c)$.
</div>

<div class="proof"><p>
1. Note that $\zero = \ntimes(\zero,a)$.
2. We have $c \in \nats$ such that $a = \ntimes(c,\zero) = \zero$.
3. Note that $a = \ntimes(a,\next(\zero))$.
4. Note that $a = \ntimes(\next(\zero),a)$.
5. First suppose $a = \zero$. Since $\ndiv(a,b)$, we have $b = 0$ as needed. Now suppose $a = \next(d)$. We have $h,k \in \nats$ such that $a = \ntimes(h,b)$ and $b = \ntimes(k,a)$; now
$$\begin{eqnarray*}
 &   & \ntimes(\next(\zero),\next(d)) \\
 & = & \next(d) \\
 & = & b \\
 & = & \ntimes(\ntimes(h,k),b) \\
 & = & \ntimes(\ntimes(h,k),\next(d));
\end{eqnarray*}$$
so we have $\ntimes(h,k) = \next(\zero)$, and thus $h = k = \next(\zero)$, so that $a = b$ as claimed.
6. We have $h,k \in \nats$ such that $\b = \ntimes(h,a)$ and $c = \ntimes(k,b)$. now $$c = \ntimes(\ntimes(h,k),a),$$ and thus $\ndiv(a,c)$.
</p></div>
</div>

And $\ndiv$ interacts with the rest of arithmetic.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. We have the following.

1. $\ndiv(a,\ntimes(b,a))$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$ then $\ndiv(c,\nplus(a,b))$.
3. If $b \neq \zero$ and $\ndiv(a,b)$ then $\nleq(a,b)$.
</div>

<div class="proof"><p>
1. We have $\ntimes(b,a) = \ntimes(b,a)$.
2. Say $a = \ntimes(h,c)$ and $b = \ntimes(k,c)$. Then by distributivity we have
$$\begin{eqnarray*}
 &   & \nplus(a,b) \\
 & = & \nplus(\ntimes(h,c),\ntimes(k,c)) \\
 & = & \ntimes(\nplus(h,k),c)
\end{eqnarray*}$$
as needed.
3. Say $b = \ntimes(k,a)$; since $b \neq \zero$, we must also have $k \neq \zero$; say $k = \next(d)$. Then
$$\begin{eqnarray*}
 &   & b \\
 & = & \ntimes(k,a) \\
 & = & \ntimes(\next(k),a) \\
 & = & \nplus(\ntimes(k,a),a)
\end{eqnarray*}$$
so that $\nleq(a,b)$.
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``div``:

> div :: (Natural t) => t -> t -> Bool
> div a b = (rem b a) == zero

Property tests:

> -- div(a,0)
> _test_div_zero_right :: (Natural t) => t -> t -> Bool
> _test_div_zero_right _ a =
>   div a zero
> 
> 
> -- div(next(0),a)
> _test_div_one_left :: (Natural t) => t -> t -> Bool
> _test_div_one_left _ a =
>   div (next zero) a
> 
> 
> -- div(a,a)
> _test_div_reflexive :: (Natural t) => t -> t -> Bool
> _test_div_reflexive _ a =
>   div a a
> 
> 
> -- div(a,times(a,b))
> _test_div_times :: (Natural t) => t -> t -> t -> Bool
> _test_div_times _ a b =
>   div a (times a b)

And the suite:

> -- run all tests for div
> _test_div :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_div t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_div_zero_right t)
>   , quickCheckWith args (_test_div_one_left t)
>   , quickCheckWith args (_test_div_reflexive t)
>   , quickCheckWith args (_test_div_times t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
