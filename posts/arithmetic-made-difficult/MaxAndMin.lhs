---
title: Maximum and Minimum
author: nbloomf
date: 2017-04-07
tags: arithmetic-made-difficult, literate-haskell
---

> module MaxAndMin
>   ( max, min, _test_max_min, main_max_min
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> import Minus
> 
> import Prelude ()
> import Test.QuickCheck

With $\nleq$ in hand we can also define max and min functions. These are less interesting since they do not have to be defined recursively. :)

<div class="result">
<div class="defn"><p>
We define $\nmax : \nats \times \nats \rightarrow \nats$ by $$\nmax(a,b) = \left\{ \begin{array}{ll} b & \mathrm{if}\ \nleq(a,b) \\ a & \mathrm{otherwise} \end{array} \right.$$ and $\nmin : \nats \times \nats \rightarrow \nats$ by $$\nmin(a,b) = \left\{ \begin{array}{ll} a & \mathrm{if}\ \nleq(a,b) \\ b & \mathrm{otherwise.} \end{array} \right.$$

In Haskell:

> max :: (Natural t) => t -> t -> t
> max a b = if leq a b then b else a
> 
> min :: (Natural t) => t -> t -> t
> min a b = if leq a b then a else b

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
8. If $\nleq(a,c)$ and $\nleq(b,c)$, then $\nleq(\nmax(a,b),c)$.
</div>

<div class="proof"><p>
1. Note that $\nleq(\zero,a)$, so that $\nmax(\zero,a) = a$.
2. We have $\nleq(a,a)$ as needed.
3. If $\nleq(a,b)$ is true, then $\nmax(a,b) = b$. If $\nleq(b,a)$ is true, then we have $a = b$ by antisymmetry and thus $$\nmax(b,a) = a = b = \nmax(a,b)$$ as needed. If $\nleq(b,a)$ is false, then $$\nmax(b,a) = b = \nmax(a,b)$$ as needed. Suppose then that $\nleq(a,b)$ is false; then $\nleq(b,a)$ is true, and we have $$\nmax(a,b) = a = \nmax(b,a).$$
4. Suppose $\nleq(\next(a),\next(b))$ is true. Then $\nleq(a,b)$, and we have $\nmax(a,b) = b$. Then $$\next(\nmax(a,b)) = \next(b) = \nmax(\next(a),\next(b)).$$ Suppose instead that $$\nleq(\next(a),\next(b))$$ is false; then $\nleq(\next(b),\next(a))$ is true, so that $\nleq(b,a)$ is true and $\nmax(a,b) = a$. Then $$\next(\nmax(a,b)) = \next(a) = \nmax(\next(a),\next(b))$$ as claimed.
5. We induct on $c$. For the base case $c = \zero$, we have $$\begin{eqnarray*} & & \nmax(\nplus(\zero,a),\nplus(\zero,b)) \\ & = & \nmax(a,b) \\ & = & \nplus(\zero,\nmax(a,b)) \end{eqnarray*}$$ as needed. For the inductive step, suppose the equation holds for some $c$. Then $$\begin{eqnarray*} & & \nmax(\nplus(\next(c),a),\nplus(\next(c),b)) \\ & = & \nmax(\next(\nplus(c,a),\next(\nplus(c,b))) \\ & = & \next(\nmax(\nplus(c,a),\nplus(c,b))) \\ & = & \next(\nplus(c,\nmax(a,b))) \\ & = & \nplus(\next(c),\nmax(a,b)) \end{eqnarray*}$$ as needed.
6. We induct on $a$. For the base case $a = \zero$, we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,a),\ntimes(c,b)) \\ & = & \nmax(\zero,\ntimes(c,b)) \\ & = & \ntimes(c,b) \\ & = & \ntimes(c,\nmax(\zero,b)) \\ & = & \ntimes(c,\nmax(a,b)) \end{eqnarray*}$$ as needed. Suppose the equality holds for some $a \in \nats$; now we induct on $b$. For the base case $b = \zero$ we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,\next(a)),\ntimes(c,b)) \\ & = & \nmax(\ntimes(c,\next(a)),\zero) \\ & = & \ntimes(c,\next(a)) \\ & = & \ntimes(c,\nmax(\next(a),\zero)) \\ & = & \ntimes(c,\nmax(\next(a),b)) \end{eqnarray*}$$ as needed. For the inductive step, suppose the equality holds for some $b$. Then we have $$\begin{eqnarray*} & & \nmax(\ntimes(c,\next(a)),\ntimes(c,\next(b))) \\ & = & \nmax(\nplus(\ntimes(c,a),c),\nplus(\ntimes(c,b),c)) \\ & = & \nplus(\nmax(\ntimes(c,a),\ntimes(c,b)),c) \\ & = & \nplus(\ntimes(c,\nmax(a,b)),c) \\ & = & \ntimes(c,\next(\nmax(a,b))) \\ & = & \ntimes(c,\nmax(\next(a),\next(b))) \end{eqnarray*}$$ as needed.
7. Brute force time! Suppose first that $\nleq(a,b) = \btrue$. If $\nleq(b,c) = \btrue$, then $\nleq(a,c) = \btrue$ by transitivity, and we have $$\begin{eqnarray*} & & \nmax(a,\nmax(b,c)) \\ & = & \nmax(a,c) \\ & = & c \\ & = & \nmax(b,c) \\ & = & \nmax(\nmax(a,b),c). \end{eqnarray*}$$ If $\nleq(b,c) = \bfalse$, then $\nleq(c,b) = \btrue$, and we have $$\begin{eqnarray*} & & \nmax(a,\nmax(b,c)) \\ & = & \nmax(a,b) \\ & = & b \\ & = & \nmax(b,c) \\ & = & \nmax(\nmax(a,b),c). \end{eqnarray*}$$ Suppose then that $\nleq(a,b) = \bfalse$, so that $\nleq(b,a) = \btrue$. If $\nleq(a,c) = \btrue$, then $\nleq(b,c) = \btrue$ by transitivity and we have $$\begin{eqnarray*} & & \nmax(\nmax(a,b),c) \\ & = & \nmax(a,c) \\ & = & \nmax(a,\nmax(b,c)). \end{eqnarray*}$$ If $\nleq(a,c) = \bfalse$, then $\nleq(c,a) = \btrue$. Suppose $\nleq(b,c) = \btrue$; then we have $$\nmax(\nmax(a,b),c) = \nmax(a,c) = \nmax(a,\nmax(b,c));$$ if $\nleq(b,c)$ is false, we have $\nleq(c,b) = \btrue$, and so $$\begin{eqnarray*} & & \nmax(\nmax(a,b),c) \\ & = & \nmax(a,c) \\ & = & a \\ & = & \nmax(a,b) \\ & = & \nmax(a,\nmax(b,c)) \end{eqnarray*}$$ as needed.
8. If $\nleq(a,b) = \btrue$, then $\nmax(a,b) = b$, and if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, so that $\nmax(a,b) = a$. In either case we have $\nleq(\nmax(a,b),c)$.
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
7. $\nmin(a,\nmin(b,c)) = \nmin(\nmin(a,b),c)$.
8. If $\nleq(c,a)$ and $\nleq(c,b)$, then $\nleq(c,\nmin(a,b))$.
</div>
</div>

And $\nmax$ and $\nmin$ interact with each other:

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nleq(\nmin(a,b),\nmax(a,b)) = \btrue$.
2. $\nplus(\nmin(a,b),\nmax(a,b)) = \nplus(a,b)$.
3. $\ntimes(\nmin(a,b),\nmax(a,b)) = \ntimes(a,b)$.
4. $\nmin(a,\nmax(b,c)) = \nmax(\nmin(a,b),\nmin(a,c))$.
5. $\nmax(a,\nmin(b,c)) = \nmin(\nmax(a,b),\nmax(a,c))$.
6. $\nmin(\nmax(b,c),a) = \nmax(\nmin(b,a),\nmin(c,a))$.
7. $\nmax(\nmin(b,c),a) = \nmin(\nmax(b,a),\nmax(c,a))$.
</div>

<div class="proof"><p>
1. Suppose $\nleq(a,b)$. Now $\nmin(a,b) = a$ and $\nmax(a,b) = b$, so that $$\nleq(\nmin(a,b),\nmax(a,b)) = \nleq(a,b) = \btrue$$ as claimed. Now if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, and we instead have $\nmin(a,b) = a$ and $\nmax(a,b) = b$.
2. Similar to (1).
3. Similar to (1).
4. Brute force time! Suppose $\nleq(a,b) = \btrue$. If $\nleq(a,c) = \btrue$, then $\nleq(a,\nmin(b,c))$, so that $\nleq(a,\nmax(b,c))$. Now we have $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(a,a) \\ & = & a \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ Suppose $\nleq(a,c) = \bfalse$; then $\nleq(c,a) = \btrue$, and by transitivity $\nleq(c,b) = \btrue$ so that $\nmax(b,c) = b$. Now $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(a,c) \\ & = & a \\ & = & \nmin(a,b) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ Now suppose $\nleq(a,b) = \bfalse$, so that $\nleq(b,a) = \btrue$. If $\nleq(a,c)$, then $\nleq(b,c)$ by transitivity. So we have $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(b,a) \\ & = & a \\ & = & \nmin(a,c) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ If $\nleq(a,c) = \bfalse$, then $\nleq(c,a) = \btrue$. In this case we have $\nleq(\nmax(b,c),a)$, so that $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(b,c) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$
5. Similar to (4), which we can agree was super tedious.
6. Follows from (4) and commutativity.
7. Follows from (5) and commutativity.
</p></div>
</div>

woo!


Implementation and Testing
--------------------------

Property tests for ``max``:

> -- a == max(a,0) and a == max(0,a)
> _test_max_zero :: (Natural n)
>   => n -> Nat n -> Bool
> _test_max_zero _ a =
>   (a ==== max a zero) &&& (a ==== max zero a)
> 
> 
> -- a == max(a,a)
> _test_max_idempotent :: (Natural n)
>   => n -> Nat n -> Bool
> _test_max_idempotent _ a =
>   (max a a) ==== a
> 
> 
> -- max(a,b) == max(b,a)
> _test_max_commutative :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_max_commutative _ a b =
>   (max a b) ==== (max b a)
> 
> 
> -- max(next(a),next(b)) == next(max(a,b))
> _test_max_next :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_max_next _ a b =
>   (max (next a) (next b)) ==== next (max a b)
> 
> 
> -- max(plus(c,a),plus(c,b)) == plus(c,max(a,b))
> _test_max_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_plus _ a b c =
>   (max (plus c a) (plus c b)) ==== plus c (max a b)
> 
> 
> -- max(times(c,a),times(c,b)) == times(c,max(a,b))
> _test_max_times :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_times _ a b c =
>   (max (times c a) (times c b)) ==== times c (max a b)
> 
> 
> -- max(max(a,b),c) == max(a,max(b,c))
> _test_max_associative :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_associative _ a b c =
>   (max (max a b) c) ==== (max a (max b c))
> 
> 
> -- if leq(a,c) and leq(b,c) then leq(max(a,b),c)
> _test_max_leq :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_leq _ a b c =
>   if (leq a c) &&& (leq b c)
>     then leq (max a b) c
>     else True

Property tests for ``min``:

> -- 0 == min(a,0) and 0 == min(0,a)
> _test_min_zero :: (Natural n)
>   => n -> Nat n -> Bool
> _test_min_zero _ a =
>   (zero ==== min a zero) &&& (zero ==== min zero a)
> 
> 
> -- a == min(a,a)
> _test_min_idempotent :: (Natural n)
>   => n -> Nat n -> Bool
> _test_min_idempotent _ a =
>   (min a a) ==== a
> 
> 
> -- min(a,b) == min(b,a)
> _test_min_commutative :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_min_commutative _ a b =
>   (min a b) ==== (min b a)
> 
> 
> -- min(next(a),next(b)) == next(min(a,b))
> _test_min_next :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_min_next _ a b =
>   (min (next a) (next b)) ==== next (min a b)
> 
> 
> -- min(plus(c,a),plus(c,b)) == plus(c,min(a,b))
> _test_min_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_plus _ a b c =
>   (min (plus c a) (plus c b)) ==== plus c (min a b)
> 
> 
> -- min(times(c,a),times(c,b)) == times(c,min(a,b))
> _test_min_times :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_times _ a b c =
>   (min (times c a) (times c b)) ==== times c (min a b)
> 
> 
> -- min(min(a,b),c) == min(a,min(b,c))
> _test_min_associative :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_associative _ a b c =
>   (min (min a b) c) ==== (min a (min b c))
> 
> 
> -- if leq(c,a) and leq(c,b) then leq(c,min(a,b))
> _test_min_leq :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_leq _ a b c =
>   if (leq c a) &&& (leq c b)
>     then leq c (min a b)
>     else True

And property tests using both:

> -- leq(min(a,b),max(a,b))
> _test_max_min_leq :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_max_min_leq _ a b =
>   leq (min a b) (max a b)
> 
> 
> -- plus(min(a,b),max(a,b)) == plus(a,b)
> _test_max_min_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_max_min_plus _ a b =
>   (plus (min a b) (max a b)) ==== (plus a b)
> 
> 
> -- times(min(a,b),max(a,b)) == times(a,b)
> _test_max_min_times :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_max_min_times _ a b =
>   (times (min a b) (max a b)) ==== (times a b)
> 
> 
> -- max(a,min(b,c)) == min(max(a,b),max(a,c))
> _test_max_min_distributive_left :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_min_distributive_left _ a b c =
>   (max a (min b c)) ==== (min (max a b) (max a c))
> 
> 
> -- max(min(b,c),a) == min(max(b,a),max(c,a))
> _test_max_min_distributive_right :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_max_min_distributive_right _ a b c =
>   (max (min b c) a) ==== (min (max b a) (max c a))
> 
> 
> -- min(a,max(b,c)) == max(min(a,b),min(a,c))
> _test_min_max_distributive_left :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_max_distributive_left _ a b c =
>   (min a (max b c)) ==== (max (min a b) (min a c))
> 
> 
> -- min(max(b,c),a) == max(min(b,a),min(c,a))
> _test_min_max_distributive_right :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_min_max_distributive_right _ a b c =
>   (min (max b c) a) ==== (max (min b a) (min c a))

And the suite for ``max`` and ``min``:

> -- run all tests for max
> _test_max_min ::
>   ( TypeName n, Natural n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_max_min n maxSize numCases = do
>   testLabel ("min & max: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_max_zero n)
>   runTest args (_test_max_idempotent n)
>   runTest args (_test_max_commutative n)
>   runTest args (_test_max_next n)
>   runTest args (_test_max_plus n)
>   runTest args (_test_max_times n)
>   runTest args (_test_max_associative n)
>   runTest args (_test_max_leq n)
> 
>   runTest args (_test_min_zero n)
>   runTest args (_test_min_idempotent n)
>   runTest args (_test_min_commutative n)
>   runTest args (_test_min_next n)
>   runTest args (_test_min_plus n)
>   runTest args (_test_min_times n)
>   runTest args (_test_min_associative n)
>   runTest args (_test_min_leq n)
> 
>   runTest args (_test_max_min_leq n)
>   runTest args (_test_max_min_plus n)
>   runTest args (_test_max_min_times n)
>   runTest args (_test_max_min_distributive_left n)
>   runTest args (_test_max_min_distributive_right n)
>   runTest args (_test_min_max_distributive_left n)
>   runTest args (_test_min_max_distributive_right n)

> main_max_min :: IO ()
> main_max_min = do
>   _test_max_min (zero :: Unary) 100 100
