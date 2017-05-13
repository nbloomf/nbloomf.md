---
title: Divides
author: nbloomf
date: 2017-04-09
tags: arithmetic-made-difficult, literate-haskell
---

> module Divides
>   ( div, _test_div, main_div
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> import DivisionAlgorithm
> 
> import Prelude (Show, Int, IO, sequence_)
> import Test.QuickCheck

With the division algorithm in hand we can define what it means for one natural number to divide another.

<div class="result">
<div class="defn"><p>
We define $\ndiv : \nats \times \nats \rightarrow \bool$ by $$\ndiv(a,b) = \iszero(\nrem(b,a)).$$
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
6. We have $h,k \in \nats$ such that $b = \ntimes(h,a)$ and $c = \ntimes(k,b)$. now $$c = \ntimes(\ntimes(h,k),a),$$ and thus $\ndiv(a,c)$.
</p></div>
</div>

And $\ndiv$ interacts with the rest of arithmetic.

<div class="result">
<div class="thm">
Let $a,b,c,d \in \nats$. We have the following.

1. $\ndiv(a,\ntimes(b,a))$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$ then $\ndiv(c,\nplus(a,b))$.
3. If $\ndiv(d,a)$ and $\ndiv(d,c)$ and $\nplus(a,b) = c$, then $\ndiv(d,b)$.
4. If $b \neq \zero$ and $\ndiv(a,b)$ then $\nleq(a,b)$.
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
3. We consider two cases: either $d = \zero$ or $d = \next(m)$ for some $m$. If $d = \zero$, then we have $a = c = \zero$, and thus $b = \zero$. So $\ndiv(d,b)$ as claimed. Suppose now that $d = \next(m)$. Now $a = \ntimes(d,u)$ and $c = \ntimes(d,v)$ for some $u$ and $v$. Letting $(q,r) = \ndivalg(b,d)$, we have $$b = \nplus(\ntimes(q,d),r.$$ Now
$$\begin{eqnarray*}
 &   & \ntimes(d,v) \\
 & = & c \\
 & = & \nplus(a,b) \\
 & = & \nplus(\ntimes(d,u),\nplus(\ntimes(q,d),r)) \\
 & = & \nplus(\ntimes(d,\nplus(u,q)),r)
\end{eqnarray*}$$
so that $$r = \nminus(\ntimes(d,v),\ntimes(d,\nplus(u,q))) = \ntimes(d,\nminus(v,\nplus(u,q))).$$ Now $\nleq(r,m)$, so if $\nminus(v,\nplus(u,q)) \neq \zero$ we have $\nleq(\next(m),m)$, a contradiction. So we must have $\nminus(v,\nplus(u,q)) = \zero$, and thus $r = \zero$. So $\ndiv(d,b)$ as claimed.
4. Say $b = \ntimes(k,a)$; since $b \neq \zero$, we must also have $k \neq \zero$; say $k = \next(d)$. Then
$$\begin{eqnarray*}
 &   & b \\
 & = & \ntimes(k,a) \\
 & = & \ntimes(\next(k),a) \\
 & = & \nplus(\ntimes(k,a),a)
\end{eqnarray*}$$
so that $\nleq(a,b)$.
</p></div>
</div>

Some more.

<div class="result">
<div class="thm">
Let $a,b,c,d \in \nats$. Then we have the following.

1. If $\ndiv(b,a)$ and $c \neq \zero$, then $$\nquo(\ntimes(a,c),\ntimes(b,c)) = \nquo(a,b).$$
2. If $\ndiv(b,a)$, then $\nquo(\ntimes(c,a),b) = \ntimes(c,\nquo(a,b))$.
3. If $\ndiv(c,a)$, $n \neq \zero$, and $\ntimes(a,b) = \ntimes(c,d)$, then $\ndiv(b,d)$.
</div>

<div class="proof"><p>
1. We consider two cases: either $b = \zero$ or $b \neq \zero$. If $b = \zero$ then we have $a = \zero$, and
$$\begin{eqnarray*}
 &   & \nquo(a,b) \\
 & = & \nquo(\zero,\zero) \\
 & = & \nquo(\ntimes(\zero,c),\ntimes(\zero,c)) \\
 & = & \nquo(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed. Suppose instead that $b \neq \zero$; say $b = \next(m)$. Since $\ndiv(b,a)$, we have $a = \ntimes(d,b)$ for some $d$; since $\nleq(\zero,m)$, by the uniqueness of quotients by nonzero divisors we have $d = \nquo(a,b)$. But also $$\ntimes(a,c) = \ntimes(d,\ntimes(b,c)),$$ and since $\ntimes(b,c) \neq \zero$ we again have $$d = \nquo(\ntimes(a,c),\ntimes(b,c))$$ by the uniqueness of quotients by nonzero divisors. Thus $$\nquo(a,b) = \nquo(\ntimes(a,c),\ntimes(b,c))$$ as claimed.
2. We consider two cases: either $b = \zero$ or $b \neq \zero$. If $b = \zero$, we have $a = \zero$. Now
$$\begin{eqnarray*}
 &   & \nquo(\ntimes(c,a),b) \\
 & = & \nquo(\zero,\zero) \\
 & = & \zero \\
 & = & \ntimes(c,\zero) \\
 & = & \ntimes(c,\nquo(a,b))
\end{eqnarray*}$$
as claimed. Suppose then that $b \neq \zero$; say $b = \next(m)$. Now say $a = \ntimes(q,b)$, and by the uniqueness of quotients by a nonzero divisor, we have $q = \nquo(a,b)$. Now $\ntimes(c,a) = \ntimes(\ntimes(c,q),b)$, and again by the uniqueness of quotients by a nonzero divisor we have
$$\begin{eqnarray*}
 &   & \nquo(\ntimes(c,a),b) \\
 & = & \ntimes(c,q) \\
 & = & \ntimes(c,\nquo(a,b))
\end{eqnarray*}$$
as claimed.
3. Say $a = \ntimes(c,u)$. Now $$\ntimes(c,\ntimes(u,b)) = \ntimes(c,d),$$ so that $d = \ntimes(u,b)$. Thus $\ndiv(b,d)$ as claimed.
</p></div>
</div>

We'll call the next result the Cross Multiplication Theorem.

<div class="result">
<div class="thm">
Let $a,b,c,d \in \nats$ such that $\ndiv(b,a)$ and $\ndiv(d,c)$ and $b, d \neq \zero$. Then $$\ntimes(a,d) = \ntimes(b,c)$$ if and only if $\nquo(a,b) = \nquo(c,d).$$
</div>

<div class="proof"><p>
Since $b$ and $d$ are both not zero, using the uniqueness of quotients by nonzero divisors we have $$\ntimes(a,d) = \ntimes(b,c)$$ if and only if $$\nquo(\ntimes(a,d),b) = c$$ if and only if $$\ntimes(d,\nquo(a,b)) = c$$ if and only if $$\nquo(a,b) = \nquo(c,d)$$ as claimed.
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``div``:

> div :: (Natural t) => t -> t -> Bool
> div a b = isZero (rem b a)

Property tests:

> -- div(a,0)
> _test_div_zero_right :: (Natural n)
>   => n -> Nat n -> Bool
> _test_div_zero_right _ a =
>   div a zero
> 
> 
> -- div(next(0),a)
> _test_div_one_left :: (Natural n)
>   => n -> Nat n -> Bool
> _test_div_one_left _ a =
>   div (next zero) a
> 
> 
> -- div(a,a)
> _test_div_reflexive :: (Natural n)
>   => n -> Nat n -> Bool
> _test_div_reflexive _ a =
>   div a a
> 
> 
> -- div(a,times(a,b))
> _test_div_times :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
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

> main_div :: IO ()
> main_div = _test_div (zero :: Unary) 50 100
