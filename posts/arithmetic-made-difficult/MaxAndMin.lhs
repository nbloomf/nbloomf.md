---
title: Maximum and Minimum
author: nbloomf
date: 2017-04-07
tags: arithmetic-made-difficult, literate-haskell
---

> module MaxAndMin
>   ( max, min, _test_max_min
>   ) where
>
> import Prelude hiding (max, min)
>
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> import Minus
> 
> import Test.QuickCheck

With $\nleq$ in hand we can also define max and min functions. These are less interesting since they do not have to be defined recursively. :)

<div class="result">
<div class="defn"><p>
We define $\nmax : \nats \times \nats \rightarrow \nats$ by $$\nmax(a,b) = \left\{ \begin{array}{ll} b & \mathrm{if}\ \nleq(a,b) \\ a & \mathrm{otherwise} \end{array} \right.$$ and $\nmin : \nats \times \nats \rightarrow \nats$ by $$\nmin(a,b) = \left\{ \begin{array}{ll} a & \mathrm{if}\ \nleq(a,b) \\ b & \mathrm{otherwise.} \end{array} \right.$$
</p></div>
</div>

Here we go.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmax(\zero,a) = a$.
2. $\nmax(a,a) = a$.
3. $\nmax(a,b) = \nmax(b,a)$.
4. $\nmax(\next(a),\next(b)) = \next(\nmax(a,b))$.
5. $\nmax(\nplus(c,a),\nplus(c,b)) = \nplus(c,\nmax(a,b))$.
6. $\nmax(\ntimes(c,a),\ntimes(c,b)) = \ntimes(c,\nmax(a,b))$.
7. $\nmax(a,\nmax(b,c)) = \nmax(\nmax(a,b),c)$.
</div>

<div class="proof"><p>
1. Note that $\nleq(\zero,a)$, so that $\nmax(\zero,a) = a$.
2. We have $\nleq(a,a)$ as needed.
3. If $\nleq(a,b)$ is true, then $\nmax(a,b) = b$. If $\nleq(b,a)$ is true, then we have $a = b$ by antisymmetry and thus $$\nmax(b,a) = a = b = \nmax(a,b)$$ as needed. If $\nleq(b,a)$ is false, then $$\nmax(b,a) = b = \nmax(a,b)$$ as needed. Suppose then that $\nleq(a,b)$ is false; then $\nleq(b,a)$ is true, and we have $$\nmax(a,b) = a = \nmax(b,a).$$
4. Suppose $\nleq(\next(a),\next(b))$ is true. Then $\nleq(a,b)$, and we have $\nmax(a,b) = b$. Then $$\next(\nmax(a,b)) = \next(b) = \nmax(\next(a),\next(b)).$$ Suppose instead that $$\nleq(\next(a),\next(b))$$ is false; then $\nleq(\next(b),\next(a))$ is true, so that $\nleq(b,a)$ is true and $\nmax(a,b) = a$. Then $$\next(\nmax(a,b)) = \next(a) = \nmax(\next(a),\next(b))$$ as claimed.
5. We induct on $c$. For the base case $c = \zero$, we have $$\begin{eqnarray*} & & \nmax(\nplus(\zero,a),\nplus(\zero,b)) \\ & = & \nmax(a,b) \\ & = & \nplus(\zero,\nmax(a,b)) \end{eqnarray*}$$ as needed. For the inductive step, suppose the equation holds for some $c$. Then $$\begin{eqnarray*} & & \nmax(\nplus(\next(c),a),\nplus(\next(c),b)) \\ & = & \nmax(\next(\nplus(c,a),\next(\nplus(c,b))) \\ & = & \next(\nmax(\nplus(c,a),\nplus(c,b))) \\ & = & \next(\nplus(c,\nmax(a,b))) \\ & = & \nplus(\next(c),\nmax(a,b)) \end{eqnarray*}$$ as needed.
6. We induct on $a$. For the base case $a = \zero$, we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,a),\ntimes(c,b)) \\ & = & \nmax(\zero,\ntimes(c,b)) \\ & = & \ntimes(c,b) \\ & = & \ntimes(c,\nmax(\zero,b)) \\ & = & \ntimes(c,\nmax(a,b)) \end{eqnarray*}$$ as needed. Suppose the equality holds for some $a \in \nats$; now we induct on $b$. For the base case $b = \zero$ we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,\next(a)),\ntimes(c,b)) \\ & = & \nmax(\ntimes(c,\next(a)),\zero) \\ & = & \ntimes(c,\next(a)) \\ & = & \ntimes(c,\nmax(\next(a),\zero)) \\ & = & \ntimes(c,\nmax(\next(a),b)) \end{eqnarray*}$$ as needed. For the inductive step, suppose the equality holds for some $b$. Then we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,\next(a)),\ntimes(c,\next(b))) \\ & = & \nmax(\nplus(\ntimes(c,a),c),\nplus(\ntimes(c,b),c)) \\ & = & \nplus(\nmax(\ntimes(c,a),\ntimes(c,b)),c) \\ & = & \nplus(\ntimes(c,\nmax(a,b)),c) \\ & = & \ntimes(c,\next(\nmax(a,b))) \\ & = & \ntimes(c,\nmax(\next(a),\next(b))) \end{eqnarray*}$$ as needed.
7. Brute force time! Suppose first that $\nleq(a,b) = \btrue$. If $\nleq(b,c) = \btrue$, then $\nleq(a,c) = \btrue$ by transitivity, and we have $$\begin{eqnarray*} & & \nmax(a,\nmax(b,c)) \\ & = & \nmax(a,c) \\ & = & c \\ & = & \nmax(b,c) \\ & = & \nmax(\nmax(a,b),c). \end{eqnarray*}$$ If $\nleq(b,c) = \bfalse$, then $\nleq(c,b) = \btrue$, and we have $$\begin{eqnarray*} & & \nmax(a,\nmax(b,c)) \\ & = & \nmax(a,b) \\ & = & b \\ & = & \nmax(b,c) \\ & = & \nmax(\nmax(a,b),c). \end{eqnarray*}$$ Suppose then that $\nleq(a,b) = \bfalse$, so that $\nleq(b,a) = \btrue$. If $\nleq(a,c) = \btrue$, then $\nleq(b,c) = \btrue$ by transitivity and we have $$\begin{eqnarray*} & & \nmax(\nmax(a,b),c) \\ & = & \nmax(a,c) \\ & = & \nmax(a,\nmax(b,c)). \end{eqnarray*}$$ If $\nleq(a,c) = \bfalse$, then $\nleq(c,a) = \btrue$. Suppose $\nleq(b,c) = \btrue$; then we have $$\nmax(\nmax(a,b),c) = \nmax(a,c) = \nmax(a,\nmax(b,c));$$ if $\nleq(b,c)$ is false, we have $\nleq(c,b) = \btrue$, and so $$\begin{eqnarray*} & & \nmax(\nmax(a,b),c) \\ & = & \nmax(a,c) \\ & = & a \\ & = & \nmax(a,b) \\ & = & \nmax(a,\nmax(b,c)) \end{eqnarray*}$$ as needed.
</p></div>
</div>

Analogous statements with analogous proofs also hold for $\nmin$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmin(\zero,a) = \zero$.
2. $\nmin(a,a) = a$.
3. $\nmin(a,b) = \nmin(b,a)$.
4. $\nmin(\next(a),\next(b)) = \next(\nmin(a,b))$.
5. $\nmin(\nplus(c,a),\nplus(c,b)) = \nplus(c,\nmin(a,b))$.
6. $\nmin(\ntimes(c,a),\ntimes(c,b)) = \ntimes(c,\nmin(a,b))$.
</div>
</div>

And $\nmax$ and $\nmin$ interact with each other:

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nleq(\nmin(a,b),\nmax(a,b)) = \btrue$.
2. $\nplus(\nmin(a,b),\nmax(a,b)) = \nplus(a,b)$.
2. $\ntimes(\nmin(a,b),\nmax(a,b)) = \ntimes(a,b)$.
</div>

<div class="proof"><p>
1. Suppose $\nleq(a,b)$. Now $\nmin(a,b) = a$ and $\nmax(a,b) = b$, so that $$\nleq(\nmin(a,b),\nmax(a,b)) = \nleq(a,b) = \btrue$$ as claimed.
2. 
3. 
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``max`` and ``min``:

> max :: (Natural t) => t -> t -> t
> max a b = if leq a b then b else a
> 
> 
> min :: (Natural t) => t -> t -> t
> min a b = if leq a b then a else b

Property tests for ``max``:

> -- a == max(a,0) and a == max(0,a)
> _test_max_zero :: (Natural t) => t -> t -> Bool
> _test_max_zero _ a = and
>   [ a == max a zero
>   , a == max zero a
>   ]
> 
> 
> -- a == max(a,a)
> _test_max_idempotent :: (Natural t) => t -> t -> Bool
> _test_max_idempotent _ a =
>   (max a a) == a
> 
> 
> -- max(a,b) == max(b,a)
> _test_max_commutative :: (Natural t) => t -> t -> t -> Bool
> _test_max_commutative _ a b =
>   (max a b) == (max b a)
> 
> 
> -- max(next(a),next(b)) == next(max(a,b))
> _test_max_next :: (Natural t) => t -> t -> t -> Bool
> _test_max_next _ a b =
>   (max (next a) (next b)) == next (max a b)
> 
> 
> -- max(plus(c,a),plus(c,b)) == plus(c,max(a,b))
> _test_max_plus :: (Natural t) => t -> t -> t -> t -> Bool
> _test_max_plus _ a b c =
>   (max (plus c a) (plus c b)) == plus c (max a b)
> 
> 
> -- max(times(c,a),times(c,b)) == times(c,max(a,b))
> _test_max_times :: (Natural t) => t -> t -> t -> t -> Bool
> _test_max_times _ a b c =
>   (max (times c a) (times c b)) == times c (max a b)
> 
> 
> -- max(max(a,b),c) == max(a,max(b,c))
> _test_max_associative :: (Natural t) => t -> t -> t -> t -> Bool
> _test_max_associative _ a b c =
>   (max (max a b) c) == (max a (max b c))

Property tests for ``min``:

And property tests using both:

> -- leq(min(a,b),max(a,b))
> _test_max_min_leq :: (Natural t) => t -> t -> t -> Bool
> _test_max_min_leq _ a b =
>   leq (min a b) (max a b)
> 
> 
> -- plus(min(a,b),max(a,b)) == plus(a,b)
> _test_max_min_plus :: (Natural t) => t -> t -> t -> Bool
> _test_max_min_plus _ a b =
>   (plus (min a b) (max a b)) == (plus a b)
> 
> 
> -- times(min(a,b),max(a,b)) == times(a,b)
> _test_max_min_times :: (Natural t) => t -> t -> t -> Bool
> _test_max_min_times _ a b =
>   (times (min a b) (max a b)) == (times a b)

And the suite for ``max`` and ``min``:

> -- run all tests for max
> _test_max_min :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_max_min t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_max_zero t)
>   , quickCheckWith args (_test_max_idempotent t)
>   , quickCheckWith args (_test_max_commutative t)
>   , quickCheckWith args (_test_max_next t)
>   , quickCheckWith args (_test_max_plus t)
>   , quickCheckWith args (_test_max_times t)
>   , quickCheckWith args (_test_max_associative t)
> 
>   , quickCheckWith args (_test_max_min_leq t)
>   , quickCheckWith args (_test_max_min_plus t)
>   , quickCheckWith args (_test_max_min_times t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
