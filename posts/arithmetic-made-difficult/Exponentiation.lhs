---
title: Exponentiation
author: nbloomf
date: 2017-04-14
tags: arithmetic-made-difficult, literate-haskell
slug: power
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Exponentiation
>   ( power, _test_power, main_power
>   ) where
>
> import Testing
> import Booleans
> import NaturalNumbers
> import SimpleRecursion
> import Plus
> import Times

We defined $\ntimes$ as iterated addition; similarly, exponentiation is iterated multiplication. We'll call this function $\npower$.

:::::: definition ::
Define $\varphi : \nats \rightarrow \nats$ by $\varphi(a) = \next(\zero)$, and define $\mu : \nats \times \nats \times \nats \rightarrow \nats$ by $\mu(k,a,b) = \ntimes(b,a)$. We define $\npower : \nats \times \nats \rightarrow \nats$ by $$\npower(a,b) = \simprec(\varphi)(\mu)(b,a).$$

In Haskell:

> power :: (Natural n) => n -> n -> n
> power a b = simpleRec phi mu b a
>   where
>     phi _     = next zero
>     mu  _ c d = times d c

::::::::::::::::::::

Because $\npower$ is defined in terms of simple recursion, it is the unique solution to a system of functional equations.

:::::: corollary :::
$\npower$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(a,\zero) = \next(\zero) \\
 f(a,\next(b)) = \ntimes(f(a,b),a).
\end{array}\right.$$

::: test :::::::::::

> _test_power_zero_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_power_zero_right _ =
>   testName "power(a,zero) == next(zero)" $
>   \a -> eq (power a zero) (next zero)
> 
> 
> _test_power_next_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_power_next_right _ =
>   testName "power(a,next(b)) == times(power(a,b),a)" $
>   \a b -> eq (power a (next b)) (times (power a b) a)

::::::::::::::::::::
::::::::::::::::::::

Some special cases.

:::::: theorem :::::
Let $a \in \nats$. Then we have the following.

1. $\npower(a,\next(\zero)) = a$.
2. $\npower(\zero,\next(a)) = \zero$.
3. $\npower(\next(\zero),a) = \next(\zero)$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \npower(a,\next(\zero)) \\
 & = & \ntimes(\npower(a,\zero),a) \\
 & = & \ntimes(\next(\zero),a) \\
 &     \href{@times@#thm-times-one-left}
   = & a
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \npower(\zero,\next(a)) \\
 & = & \ntimes(\npower(\zero,a),\zero) \\
 &     \href{@times@#thm-times-zero-right}
   = & \zero
\end{eqnarray*}$$
as claimed.
3. We proceed by induction on $a$. For the base case, we have $\npower(\next(\zero),\zero) = \next(\zero)$. For the inductive step, suppose $\npower(\next(\zero),a) = \next(\zero)$. Now
$$\begin{eqnarray*}
 &   & \npower(\next(\zero),\next(a)) \\
 & = & \ntimes(\npower(\next(\zero),a),\next(\zero)) \\
 &     \href{@times@#thm-times-one-right}
   = & \npower(\next(\zero),a) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_power_one_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_power_one_right _ =
>   testName "power(a,1) == a" $
>   \a -> eq (power a (next zero)) a
> 
> 
> _test_power_zero_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_power_zero_left _ =
>   testName "power(zero,next(a)) == zero" $
>   \a -> eq (power zero (next a)) zero
> 
> 
> _test_power_one_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_power_one_left _ =
>   testName "power(next(zero),a) == next(zero)" $
>   \a -> eq (power (next zero) a) (next zero)

::::::::::::::::::::
::::::::::::::::::::

And interaction with $\nplus$ and $\ntimes$.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have the following.

1. $\npower(a,\nplus(b,c)) = \ntimes(\npower(a,b),\npower(a,c))$.
2. $\npower(a,\ntimes(b,c)) = \npower(\npower(a,b),c)$.
3. $\npower(\ntimes(a,b),c) = \ntimes(\npower(a,c),\npower(b,c))$.

::: proof ::::::::::
1. We proceed by induction on $c$. For the base case $c = \zero$, note that
$$\begin{eqnarray*}
 &   & \npower(a,\nplus(b,c)) \\
 & = & \npower(a,\nplus(b,\zero)) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & \npower(a,b) \\
 &     \href{@times@#thm-times-one-right}
   = & \ntimes(\npower(a,b),\next(\zero)) \\
 & = & \ntimes(\npower(a,b),\npower(a,\zero)) \\
 & = & \ntimes(\npower(a,b),\npower(a,c)).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $c \in \nats$. Now
$$\begin{eqnarray*}
 &   & \npower(a,\nplus(b,\next(c))) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \npower(a,\next(\nplus(b,c))) \\
 & = & \ntimes(a,\npower(a,\nplus(b,c))) \\
 & = & \ntimes(a,\ntimes(\npower(a,b),\npower(a,c))) \\
 & = & \ntimes(\npower(a,b),\ntimes(a,\npower(a,c))) \\
 & = & \ntimes(\npower(a,b),\npower(a,\next(c)))
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $c$. For the base case $c = \zero$, note that
$$\begin{eqnarray*}
 &   & \npower(a,\ntimes(b,c)) \\
 & = & \npower(a,\ntimes(b,\zero)) \\
 &     \href{@times@#thm-times-zero-right}
   = & \npower(a,\zero) \\
 & = & \next(\zero) \\
 & = & \npower(\npower(a,b),\zero) \\
 & = & \npower(\npower(a,b),c).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $c$. Now
$$\begin{eqnarray*}
 &   & \npower(a,\ntimes(b,\next(c))) \\
 & = & \npower(a,\nplus(b,\ntimes(b,c))) \\
 & = & \ntimes(\npower(a,b),\npower(a,\ntimes(b,c))) \\
 & = & \ntimes(\npower(a,b),\npower(\npower(a,b),c)) \\
 & = & \npower(\npower(a,b),\next(c))
\end{eqnarray*}$$
as claimed.
3. We proceed by induction on $c$. For the base case, we have
$$\begin{eqnarray*}
 &   & \npower(\ntimes(a,b),c) \\
 & = & \npower(\ntimes(a,b),\zero) \\
 & = & \next(\zero) \\
 &     \href{@times@#thm-times-one-left}
   = & \ntimes(\next(\zero),\next(\zero)) \\
 & = & \ntimes(\npower(a,\zero),\npower(b,\zero)) \\
 & = & \ntimes(\npower(a,c),\npower(b,c)).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $c$. Now
$$\begin{eqnarray*}
 &   & \npower(\ntimes(a,b),\next(c)) \\
 & = & \ntimes(\ntimes(a,b),\npower(\ntimes(a,b),c)) \\
 & = & \ntimes(\ntimes(a,b),\ntimes(\npower(a,c),\npower(b,c))) \\
 & = & \ntimes(\ntimes(a,\npower(a,c))\ntimes(b,\npower(b,c))) \\
 & = & \ntimes(\npower(a,\next(c)),\npower(b,\next(c)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_power_plus_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_power_plus_right _ =
>   testName "power(a,plus(b,c)) == times(power(a,b),power(a,c))" $
>   \a b c -> eq (power a (plus b c)) (times (power a b) (power a c))
> 
> 
> _test_power_times_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_power_times_right _ =
>   testName "power(a,times(b,c)) == power(power(a,b),c)" $
>   \a b c -> eq (power a (times b c)) (power (power a b) c)
> 
> 
> _test_power_times_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_power_times_left _ =
>   testName "power(times(a,b),c) == times(power(a,c),power(b,c))" $
>   \a b c -> eq (power (times a b) c) (times (power a c) (power b c))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_power ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_power n size cases = do
>   testLabel1 "power" n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_power_zero_right n)
>   runTest args (_test_power_next_right n)
>   runTest args (_test_power_one_right n)
>   runTest args (_test_power_zero_left n)
>   runTest args (_test_power_one_left n)
>   runTest args (_test_power_plus_right n)
>   runTest args (_test_power_times_right n)
>   runTest args (_test_power_times_left n)

Main:

> main_power :: IO ()
> main_power = do
>   _test_power (zero :: Unary) 4 30
