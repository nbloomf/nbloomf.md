---
title: Multiplication
author: nbloomf
date: 2017-03-31
tags: arithmetic-made-difficult, literate-haskell
slug: times
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Times
>  ( times, _test_times, main_times
>  ) where
> 
> import Testing
> import Booleans
> import NaturalNumbers
> import SimpleRecursion
> import Plus

Natural number multiplication has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define it as $\Theta = \simprec{\varphi}{\mu}$ for some appropriate $\varphi$ and $\mu$. Using the universal property of simple recursion and how we want multiplication to behave, note that on the one hand we want $\Theta(\zero,m) = \zero$ for all $m$, while on the other hand we have $\Theta(\zero,m) = \varphi(m)$. So apparently we need $\varphi(m) = \zero$ for all $m$.

Similarly, we want $\Theta(\next(n),m) = \nplus(\Theta(n,m),m)$, but we also have $$\Theta(\next(n),m) = \mu(n,m,\Theta(n,m)).$$ So apparently we need $\mu(n,m,k) = \nplus(k,m)$.

With this in mind, we define a binary operation $\ntimes$ on $\nats$ as follows.

<div class="result">
<div class="defn"><p>
Let $\varphi : \nats \rightarrow \nats$ be given by $\varphi(m) = \zero$, and let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \nplus(b,a)$. We then define $\ntimes : \nats \times \nats \rightarrow \nats$ by $$\ntimes = \simprec{\varphi}{\mu}.$$

In Haskell:

> times :: (Natural n) => n -> n -> n
> times = simpleRec phi mu
>   where
>     phi _ = zero
>     mu _ a b = plus b a

</p></div>
</div>

Since $\ntimes$ is defined in terms of simple recursion, it is the unique solution to a set of functional equations.

<div class="result">
<div class="corollary"><p>
$\ntimes$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(\zero,b) = \zero \\
 f(\next(a),b) = \nplus(f(a,b),b).
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_times_zero_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_times_zero_left _ f =
>   testName "times(0,a) == 0" $
>   \a -> eq (f zero a) zero
> 
> 
> _test_times_next_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_times_next_left _ f =
>   testName "times(next(a),b) == plus(times(a,b),b)" $
>   \a b -> eq (f (next a) b) (plus (f a b) b)

</p></div>
</div>

Next we establish a version of the universal property of $\ntimes$ with the arguments reversed.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$ and $b$.

1. $\ntimes(a,\zero) = \zero$.
2. $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$.
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. For the base case, note that $\ntimes(\zero,\zero) = \zero$. For the inductive step, suppose we have $\ntimes(a,\zero) = \zero$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\zero) \\
 & = & \nplus(\ntimes(a,\zero),\zero) \\
 & = & \nplus(\zero,\zero) \\
 & = & \zero
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, we have
$$\begin{eqnarray*}
 &   & \ntimes(\zero,\next(b)) \\
 & = & \zero \\
 & = & \nplus(\zero,\zero) \\
 & = & \nplus(\ntimes(\zero,b),\zero)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(b)) \\
 & = & \nplus(\ntimes(a,\next(b)),\next(b)) \\
 & = & \next(\nplus(\ntimes(a,\next(b)),b)) \\
 & = & \next(\nplus(\nplus(\ntimes(a,b),a),b)) \\
 & = & \next(\nplus(\ntimes(a,b),\nplus(a,b))) \\
 & = & \next(\nplus(\ntimes(a,b),\nplus(b,a))) \\
 & = & \next(\nplus(\nplus(\ntimes(a,b),b),a)) \\
 & = & \next(\nplus(\ntimes(\next(a),b),a)) \\
 & = & \nplus(\ntimes(\next(a),b),\next(a))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_times_zero_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_times_zero_right _ f =
>   testName "0 == times(a,0)" $
>   \a -> eq (f a zero) zero
> 
> 
> _test_times_next_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_times_next_right _ f =
>   testName "times(a,next(b)) == plus(times(a,b),a)" $
>   \a b -> eq (f a (next b)) (plus (f a b) a)

</p></div>
</div>

$\next(\zero)$ is neutral under $\ntimes$.

<div class="result">
<div class="thm">
For all $a \in \nats$, we have

1. $\ntimes(\next(\zero),a) = a$.
2. $\ntimes(a,\next(\zero)) = a$.
</div>

<div class="proof"><p>
1. Note first that for all $a$, we have
$$\begin{eqnarray*}
 &   & \ntimes(\next(\zero),a) \\
 & = & \nplus(\ntimes(\zero,a),a) \\
 & = & \nplus(\zero,a) \\
 & = & a.
\end{eqnarray*}$$
2. We proceed by induction on $a$. For the base case, note that $\ntimes(\zero,\next(\zero)) = \zero$. For the inductive step, suppose we have $\ntimes(a,\next(\zero)) = a$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(\zero)) \\
 & = & \nplus(\ntimes(a,\next(\zero)),\next(\zero)) \\
 & = & \nplus(a,\next(\zero)) \\
 & = & \next(\nplus(a,\zero)) \\
 & = & \next(a)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_times_one_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_times_one_left _ f =
>   testName "a == times(1,a)" $
>   \a -> eq a (f (next zero) a)
> 
> 
> _test_times_one_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_times_one_right _ f =
>   testName "a == times(a,1)" $
>   \a -> eq a (f a (next zero))

</p></div>
</div>

$\ntimes$ is commutative.

<div class="result">
<div class="thm">
For all $a,b \in \nats$ we have $\ntimes(a,b) = \ntimes(b,a)$.
</div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case, note that $$\ntimes(\zero,b) = \zero = \ntimes(b,\zero)$$ as needed. For the inductive step, suppose we have $\ntimes(a,b) = \ntimes(b,a)$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),b) \\
 & = & \nplus(\ntimes(a,b),b) \\
 & = & \nplus(\ntimes(b,a),b) \\
 & = & \ntimes(b,\next(a))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_times_commutative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_times_commutative _ f =
>   testName "times(a,b) == times(b,a)" $
>   \a b -> eq (f a b) (f b a)

</p></div>
</div>

$\ntimes$ distributes over $\nplus$.

<div class="result">
<div class="thm">
For all $a,b,c, \in \nats$, we have the following.

1. $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$.
2. $\ntimes(\nplus(a,b),c) = \nplus(\ntimes(a,c),\ntimes(b,c))$.
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. For the base case, we have $$\ntimes(\zero,\nplus(b,c)) = \zero = \nplus(\zero,\zero) = \nplus(\ntimes(\zero,b),\ntimes(\zero,c))$$ as needed. For the inductive step, suppose we have $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$ for all $b$ and $c$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\nplus(b,c)) \\
 & = & \nplus(\ntimes(a,\nplus(b,c)),\nplus(b,c)) \\
 & = & \nplus(\nplus(\ntimes(a,b),\ntimes(a,c)),\nplus(b,c)) \\
 & = & \nplus(\nplus(\nplus(\nplus(\ntimes(a,b),\ntimes(a,c))),b),c) \\
 & = & \nplus(\nplus(\ntimes(a,b),\nplus(\ntimes(a,c),b)),c) \\
 & = & \nplus(\nplus(\ntimes(a,b),\nplus(b,\ntimes(a,c))),c) \\
 & = & \nplus(\nplus(\nplus(\ntimes(a,b),b),\ntimes(a,c)),c) \\
 & = & \nplus(\nplus(\ntimes(a,b),b),\nplus(\ntimes(a,c),c)) \\
 & = & \nplus(\ntimes(\next(a),b),\ntimes(\next(a),c))
\end{eqnarray*}$$
as needed.
2. We have
$$\begin{eqnarray*}
 &   & \ntimes(\nplus(a,b),c) \\
 & = & \ntimes(c,\nplus(a,b)) \\
 & = & \nplus(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \nplus(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_times_distributive_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_distributive_left _ f =
>   testName "times(a,plus(b,c)) == plus(times(a,b),times(a,c))" $
>   \a b c -> eq (f a (plus b c)) (plus (f a b) (f a c))
> 
> 
> _test_times_distributive_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_distributive_right _ f =
>   testName "times(plus(a,b),c) == plus(times(a,c),times(b,c))" $
>   \a b c -> eq (f (plus a b) c) (plus (f a c) (f b c))

</p></div>
</div>

$\ntimes$ is associative,

<div class="result">
<div class="thm">
For all $a,b,c \in \nats$, we have $$\ntimes(\ntimes(a,b),c) = \ntimes(a,\ntimes(b,c)).$$
</div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case, we have
$$\begin{eqnarray*}
 &   & \ntimes(\zero,\ntimes(b,c)) \\
 & = & \zero \\
 & = & \ntimes(\zero,c) \\
 & = & \ntimes(\ntimes(\zero,b),c)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\ntimes(a,\ntimes(b,c)) = \ntimes(\ntimes(a,b),c)$ for all $b$ and $c$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \ntimes(\ntimes(\next(a),b),c) \\
 & = & \ntimes(\nplus(\ntimes(a,b),b),c) \\
 & = & \nplus(\ntimes(\ntimes(a,b),c),\ntimes(b,c)) \\
 & = & \nplus(\ntimes(a,\ntimes(b,c)),\ntimes(b,c)) \\
 & = & \ntimes(\next(a),\ntimes(b,c))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_times_associative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_associative _ f =
>   testName "times(times(a,b),c) == times(a,times(b,c))" $
>   \a b c -> eq (f (f a b) c) (f a (f b c))

</p></div>
</div>

Finally, $\ntimes$ is *almost* cancellative.

<div class="result">
<div class="thm">
For all $a,b,c \in \nats$, we have the following.

1. If $\ntimes(\next(a),b) = \ntimes(\next(a),c)$ then $b = c$.
2. If $\ntimes(b,\next(a)) = \ntimes(c,\next(a))$ then $b = c$.
</div>

<div class="proof"><p>
1. This proof will be a little different: we will use induction twice; first on $b$, and then on $c$. To this end, let $$B = \{ b \in \nats \mid \forall c, \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}$$ and given $b \in \nats$ let $$C(b) = \{ c \in \nats \mid \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}.$$ We wish to show that $B = \nats$ by induction. For the base case, we need to show that $b = \zero \in B$; for this it suffices to show that $C(\zero) = \nats$, which we do by induction. For the base case $c = \zero$, we have $b = c$ regardless of $a$. For the inductive step suppose we have $c \in C(\zero)$ for some $c$. Note that
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(c)) \\
 & = & \nplus(\ntimes(a,\next(c)),\next(c)) \\
 & = & \next(\nplus(\ntimes(a,\next(c)),c))
\end{eqnarray*}$$
while $$\ntimes(\next(a),b) = \ntimes(\next(a),\zero) = \zero;$$ in particular, the statement $$\ntimes(\next(a),\next(c)) = \ntimes(\next(a),b)$$ is false, so that $\next(c) \in C(\zero)$ *vacuously*. So we have $C(\zero) = \nats$, and thus $\zero \in B$. For the inductive step, suppose we have $b \in B$; we wish to show that $\next(b) \in B$, or equivalently that $C(\next(b)) = \nats$. We proceed by induction on $c$ again. The base case $c = \zero$ holds vacuously. For the inductive step, suppose we have $c \in C(\next(b))$. Now suppose further that $$\ntimes(\next(a),\next(b)) = \ntimes(\next(a),\next(c)).$$ Note that
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(b)) \\
 & = & \nplus(\ntimes(a,\next(c),\next(c)) \\
 & = & \next(\nplus(\ntimes(\next(c),a),c)) \\
 & = & \next(\nplus(\nplus(\ntimes(c,a),a),c)) \\
 & = & \next(\nplus(\nplus(\ntimes(a,c),c),a)).
\end{eqnarray*}$$
The analogous statement holds for $b$. So we have
$$\begin{eqnarray*}
  \next(\nplus(\nplus(\ntimes(a,b),b),a)) & = & \next(\nplus(\nplus(\ntimes(a,c),c),a)) \\
  \nplus(\nplus(\ntimes(a,b),b),a) & = & \nplus(\nplus(\ntimes(a,c),c),a) \\
  \nplus(\ntimes(a,b),b) & = & \nplus(\ntimes(a,c),c) \\
  \ntimes(\next(a),b) & = & \ntimes(\next(a),c) \\
  b & = & c
\end{eqnarray*}$$
as needed.
2. Suppose $$\ntimes(b,\next(a)) = \ntimes(c,\next(a)).$$ Then we have $$\ntimes(\next(a),b) = \ntimes(\next(a),c),$$ so that b = c$ as claimed.
</p></div>

<div class="test"><p>

> _test_times_cancellative_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_cancellative_left _ f =
>   testName "if times(next(c),a) == times(next(c),b) then a == b" $
>   \a b c -> if eq (f (next c) a) (f (next c) b)
>     then eq a b
>     else True
> 
> 
> _test_times_cancellative_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_cancellative_right _ f =
>   testName "if times(a,next(c)) == plus(b,next(c)) then a == b" $
>   \a b c -> if eq (f a (next c)) (f b (next c))
>     then eq a b
>     else True

</p></div>
</div>


Testing
-------

> _test_times :: (TypeName n, Natural n, Equal n, Arbitrary n, Show n)
>   => n -> (n -> n -> n) -> Int -> Int -> IO ()
> _test_times n f maxSize numCases = do
>   testLabel1 "times" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_times_zero_left n f)
>   runTest args (_test_times_next_left n f)
>   runTest args (_test_times_zero_right n f)
>   runTest args (_test_times_next_right n f)
>   runTest args (_test_times_one_left n f)
>   runTest args (_test_times_one_right n f)
>   runTest args (_test_times_commutative n f)
>   runTest args (_test_times_distributive_left n f)
>   runTest args (_test_times_distributive_right n f)
>   runTest args (_test_times_associative n f)
>   runTest args (_test_times_cancellative_left n f)
>   runTest args (_test_times_cancellative_right n f)

I used a much smaller number of test cases this time, because these run much more slowly than the tests for ``plus``. The culprit is ``_test_times_associative``. What's happening is that multiplication of ``Nat``s is inherently slow; it's implemented as iterated addition, which itself is iterated ``N``.

The problem lies in our *representation* of the natural numbers. A better representation might make a more efficient ``times`` possible.

> main_times :: IO ()
> main_times = do
>   _test_times (zero :: Unary) times 40 100
