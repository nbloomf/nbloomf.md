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

Natural number multiplication has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define it as $\Theta = \simprec(\varphi)(\mu)$ for some appropriate $\varphi$ and $\mu$. Using the universal property of simple recursion and how we want multiplication to behave, note that on the one hand we want $\Theta(\zero,m) = \zero$ for all $m$, while on the other hand we have $\Theta(\zero,m) = \varphi(m)$. So apparently we need $\varphi(m) = \zero$ for all $m$.

Similarly, we want $\Theta(\next(n),m) = \nplus(\Theta(n,m),m)$, but we also have $$\Theta(\next(n),m) = \mu(n,m,\Theta(n,m)).$$ So apparently we need $\mu(n,m,k) = \nplus(k,m)$.

With this in mind, we define a binary operation $\ntimes$ on $\nats$ as follows.

:::::: definition ::
Let $\varphi : \nats \rightarrow \nats$ be given by $\varphi(m) = \zero$, and let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \nplus(b,a)$. We then define $\ntimes : \nats \times \nats \rightarrow \nats$ by $$\ntimes = \simprec(\varphi)(\mu).$$

In Haskell:

> times :: (Natural n) => n -> n -> n
> times = simpleRec phi mu
>   where
>     phi _ = zero
>     mu _ a b = plus b a

::::::::::::::::::::

Since $\ntimes$ is defined in terms of simple recursion, it is the unique solution to a set of functional equations.

:::::: corollary :::
[]{#cor-times-up}[]{#cor-times-up-zero}[]{#cor-times-up-next}
$\ntimes$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(\zero,b) = \zero \\
 f(\next(a),b) = \nplus(f(a,b),b).
\end{array}\right.$$

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

Next we establish a version of the universal property of $\ntimes$ with the arguments reversed.

:::::: theorem :::::
[]{#thm-times-zero-right}[]{#thm-times-next-right}
The following hold for all natural numbers $a$ and $b$.

1. $\ntimes(a,\zero) = \zero$.
2. $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$.

::: proof ::::::::::
1. We proceed by induction on $a$. For the base case, note that $\ntimes(\zero,\zero) = \zero$. For the inductive step, suppose we have $\ntimes(a,\zero) = \zero$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\zero) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\zero),\zero) \\
 &     \hyp{\ntimes(a,\zero) = \zero}
   = & \nplus(\zero,\zero) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \zero
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, we have
$$\begin{eqnarray*}
 &   & \ntimes(\zero,\next(b)) \\
 &     \href{@times@#cor-times-up-zero}
   = & \zero \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \nplus(\zero,\zero) \\
 &     \href{@times@#cor-times-up-zero}
   = & \nplus(\ntimes(\zero,b),\zero)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(b)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\next(b)),\next(b)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \next(\nplus(\ntimes(a,\next(b)),b)) \\
 &     \hyp{\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)}
   = & \next(\nplus(\nplus(\ntimes(a,b),a),b)) \\
 &     \href{@plus@#thm-plus-associative}
   = & \next(\nplus(\ntimes(a,b),\nplus(a,b))) \\
 &     \href{@plus@#thm-plus-commutative}
   = & \next(\nplus(\ntimes(a,b),\nplus(b,a))) \\
 &     \href{@plus@#thm-plus-associative}
   = & \next(\nplus(\nplus(\ntimes(a,b),b),a)) \\
 &     \href{@times@#cor-times-up-next}
   = & \next(\nplus(\ntimes(\next(a),b),a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \nplus(\ntimes(\next(a),b),\next(a))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\next(\zero)$ is neutral under $\ntimes$.

:::::: theorem :::::
[]{#thm-times-one-left}[]{#thm-times-one-right}
For all $a \in \nats$, we have

1. $\ntimes(\next(\zero),a) = a$.
2. $\ntimes(a,\next(\zero)) = a$.

::: proof ::::::::::
1. Note first that for all $a$, we have
$$\begin{eqnarray*}
 &   & \ntimes(\next(\zero),a) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(\zero,a),a) \\
 &     \href{@times@#cor-times-up-zero}
   = & \nplus(\zero,a) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & a
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $a$. For the base case, note that $\ntimes(\zero,\next(\zero)) = \zero$. For the inductive step, suppose we have $\ntimes(a,\next(\zero)) = a$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(\zero)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\next(\zero)),\next(\zero)) \\
 &     \hyp{\ntimes(a,\next(\zero)) = a}
   = & \nplus(a,\next(\zero)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \next(\nplus(a,\zero)) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & \next(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ is commutative.

:::::: theorem :::::
[]{#thm-times-commutative}
For all $a,b \in \nats$ we have $\ntimes(a,b) = \ntimes(b,a)$.

::: proof ::::::::::
We proceed by induction on $a$. For the base case, note that $$\ntimes(\zero,b) = \zero = \ntimes(b,\zero)$$ as needed. For the inductive step, suppose we have $\ntimes(a,b) = \ntimes(b,a)$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),b) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,b),b) \\
 &     \hyp{\ntimes(a,b) = \ntimes(b,a)}
   = & \nplus(\ntimes(b,a),b) \\
 &     \href{@times@#thm-times-next-right}
   = & \ntimes(b,\next(a))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_times_commutative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_times_commutative _ f =
>   testName "times(a,b) == times(b,a)" $
>   \a b -> eq (f a b) (f b a)

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ distributes over $\nplus$.

:::::: theorem :::::
[]{#thm-times-plus-distribute-left}[]{#thm-times-plus-distribute-right}
For all $a,b,c, \in \nats$, we have the following.

1. $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$.
2. $\ntimes(\nplus(a,b),c) = \nplus(\ntimes(a,c),\ntimes(b,c))$.

::: proof ::::::::::
1. We proceed by induction on $a$. For the base case, we have $$\ntimes(\zero,\nplus(b,c)) = \zero = \nplus(\zero,\zero) = \nplus(\ntimes(\zero,b),\ntimes(\zero,c))$$ as needed. For the inductive step, suppose we have $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$ for all $b$ and $c$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\nplus(b,c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\nplus(b,c)),\nplus(b,c)) \\
 &     \hyp{\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))}
   = & \nplus(\nplus(\ntimes(a,b),\ntimes(a,c)),\nplus(b,c)) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\nplus(\nplus(\ntimes(a,b),\ntimes(a,c)),b),c) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\nplus(\ntimes(a,b),\nplus(\ntimes(a,c),b)),c) \\
 &     \href{@plus@#thm-plus-commutative}
   = & \nplus(\nplus(\ntimes(a,b),\nplus(b,\ntimes(a,c))),c) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\nplus(\nplus(\ntimes(a,b),b),\ntimes(a,c)),c) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\nplus(\ntimes(a,b),b),\nplus(\ntimes(a,c),c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(\next(a),b),\nplus(\ntimes(a,c),c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(\next(a),b),\ntimes(\next(a),c))
\end{eqnarray*}$$
as needed.
2. We have
$$\begin{eqnarray*}
 &   & \ntimes(\nplus(a,b),c) \\
 &     \href{@times@#thm-times-commutative}
   = & \ntimes(c,\nplus(a,b)) \\
 &     \href{@times@#thm-times-plus-distribute-left}
   = & \nplus(\ntimes(c,a),\ntimes(c,b)) \\
 &     \href{@times@#thm-times-commutative}
   = & \nplus(\ntimes(a,c),\ntimes(c,b)) \\
 &     \href{@times@#thm-times-commutative}
   = & \nplus(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ is associative,

:::::: theorem :::::
[]{#thm-times-associative}
For all $a,b,c \in \nats$, we have $$\ntimes(\ntimes(a,b),c) = \ntimes(a,\ntimes(b,c)).$$

::: proof ::::::::::
We proceed by induction on $a$. For the base case, we have
$$\begin{eqnarray*}
 &   & \ntimes(\zero,\ntimes(b,c)) \\
 &     \href{@times@#cor-times-up-zero}
   = & \zero \\
 &     \href{@times@#cor-times-up-zero}
   = & \ntimes(\zero,c) \\
 &     \href{@times@#cor-times-up-zero}
   = & \ntimes(\ntimes(\zero,b),c)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\ntimes(a,\ntimes(b,c)) = \ntimes(\ntimes(a,b),c)$ for all $b$ and $c$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \ntimes(\ntimes(\next(a),b),c) \\
 &     \href{@times@#cor-times-up-next}
   = & \ntimes(\nplus(\ntimes(a,b),b),c) \\
 &     \href{@times@#thm-times-plus-distribute-right}
   = & \nplus(\ntimes(\ntimes(a,b),c),\ntimes(b,c)) \\
 &     \hyp{\ntimes(a,\ntimes(b,c)) = \ntimes(\ntimes(a,b),c)}
   = & \nplus(\ntimes(a,\ntimes(b,c)),\ntimes(b,c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \ntimes(\next(a),\ntimes(b,c))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_times_associative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_associative _ f =
>   testName "times(times(a,b),c) == times(a,times(b,c))" $
>   \a b c -> eq (f (f a b) c) (f a (f b c))

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ is *almost* cancellative.

:::::: theorem :::::
For all $a,b,c \in \nats$, we have the following.

1. If $\ntimes(\next(a),b) = \ntimes(\next(a),c)$ then $b = c$.
2. If $\ntimes(b,\next(a)) = \ntimes(c,\next(a))$ then $b = c$.

::: proof ::::::::::
1. This proof will be a little different: we will use induction twice; first on $b$, and then on $c$. To this end, let $$B = \{ b \in \nats \mid \forall c, \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}$$ and given $b \in \nats$ let $$C(b) = \{ c \in \nats \mid \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}.$$ We wish to show that $B = \nats$ by induction. For the base case, we need to show that $b = \zero \in B$; for this it suffices to show that $C(\zero) = \nats$, which we do by induction. For the base case $c = \zero$, we have $b = c$ regardless of $a$. For the inductive step suppose we have $c \in C(\zero)$ for some $c$. Note that
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\next(c)),\next(c)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \next(\nplus(\ntimes(a,\next(c)),c))
\end{eqnarray*}$$
while $$\ntimes(\next(a),b) = \ntimes(\next(a),\zero) = \zero;$$ in particular, the statement $$\ntimes(\next(a),\next(c)) = \ntimes(\next(a),b)$$ is false, so that $\next(c) \in C(\zero)$ *vacuously*. So we have $C(\zero) = \nats$, and thus $\zero \in B$. For the inductive step, suppose we have $b \in B$; we wish to show that $\next(b) \in B$, or equivalently that $C(\next(b)) = \nats$. We proceed by induction on $c$ again. The base case $c = \zero$ holds vacuously. For the inductive step, suppose we have $c \in C(\next(b))$. Now suppose further that $$\ntimes(\next(a),\next(b)) = \ntimes(\next(a),\next(c)).$$ Note that
$$\begin{eqnarray*}
 &   & \ntimes(\next(a),\next(c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(a,\next(c)),\next(c)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \next(\nplus(\ntimes(a,\next(c)),c)) \\
 &     \href{@times@#thm-times-commutative}
   = & \next(\nplus(\ntimes(\next(c),a),c)) \\
 &     \href{@times@#cor-times-up-next}
   = & \next(\nplus(\nplus(\ntimes(c,a),a),c)) \\
 &     \href{@times@#thm-times-commutative}
   = & \next(\nplus(\nplus(\ntimes(a,c),a),c)) \\
 &     \href{@plus@#thm-plus-associative}
   = & \next(\nplus(\ntimes(a,c),\nplus(a,c))) \\
 &     \href{@plus@#thm-plus-commutative}
   = & \next(\nplus(\ntimes(a,c),\nplus(c,a))) \\
 &     \href{@plus@#thm-plus-associative}
   = & \next(\nplus(\nplus(\ntimes(a,c),c),a))
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
::::::::::::::::::::

::: test :::::::::::

> _test_times_cancellative_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_cancellative_left _ f =
>   testName "if times(next(c),a) == times(next(c),b) then a == b" $
>   \a b c -> if eq (f (next c) a) (f (next c) b)
>     then eq a b
>     else true
> 
> 
> _test_times_cancellative_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_times_cancellative_right _ f =
>   testName "if times(a,next(c)) == plus(b,next(c)) then a == b" $
>   \a b c -> if eq (f a (next c)) (f b (next c))
>     then eq a b
>     else true

::::::::::::::::::::
::::::::::::::::::::

As a special case, $\ntimes(\next(\next(\zero)),-)$ is equivalent to a $\nplus$.

:::::: theorem :::::
[]{#thm-times-two}
For all $a \in \nats$ we have $$\ntimes(\next(\next(\zero)),a) = \nplus(a,a).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \ntimes(\next(\next(\zero)),a) \\
 &     \href{@times@#cor-times-up-next}
   = & \nplus(\ntimes(\next(\zero),a),a) \\
 &     \href{@times@#thm-times-one-left}
   = & \nplus(a,a)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_times_two_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_times_two_left _ f =
>   testName "times(next(next(zero)),a) == plus(a,a)" $
>   \a -> eq (plus a a) (f (next (next zero)) a)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

> _test_times :: (TypeName n, Natural n, Equal n, Arbitrary n, Show n)
>   => n -> (n -> n -> n) -> Int -> Int -> IO ()
> _test_times n f size cases = do
>   testLabel1 "times" n
> 
>   let args = testArgs size cases
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
>   runTest args (_test_times_two_left n f)

I used a much smaller number of test cases this time, because these run much more slowly than the tests for ``plus``. The culprit is ``_test_times_associative``. What's happening is that multiplication of ``Nat``s is inherently slow; it's implemented as iterated addition, which itself is iterated ``N``.

The problem lies in our *representation* of the natural numbers. A better representation might make a more efficient ``times`` possible.

> main_times :: IO ()
> main_times = do
>   _test_times (zero :: Unary) times 40 100
