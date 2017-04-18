---
title: Exponentiation
author: nbloomf
date: 2017-04-21
tags: arithmetic-made-difficult, literate-haskell
---

> module Exponentiation
>   ( power, _test_power
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
> import CoprimeTo
> import LeastCommonMultiple
> 
> import Test.QuickCheck

We defined $\ntimes$ as iterated addition; similarly, exponentiation is iterated multiplication. We'll call this function $\npower$.

<div class="result">
<div class="defn"><p>
Define $\varphi : \nats \rightarrow \nats$ by $\varphi(a) = \next(\zero)$, and define $\mu : \nats \times \nats \times \nats \rightarrow \nats$ by $\mu(k,a,b) = \ntimes(b,a)$. We define $\npower : \nats \times \nats \rightarrow \nats$ by $$\npower(a,b) = \simprec{\varphi}{\mu}(b,a).$$
</p></div>
</div>

Some special cases:

<div class="result">
<div class="theorem">
Let $a \in \nats$. Then we have the following.

1. $\npower(a,\zero) = \next(\zero)$.
2. $\npower(a,\next(\zero)) = a$.
3. $\npower(\zero,\next(a)) = \zero$.
4. $\npower(\next(\zero),a) = \next(\zero)$.
</div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \npower(a,\zero) \\
 & = & \simprec{\varphi}{\mu}(\zero,a) \\
 & = & \varphi(a) \\
 & = & \next(\zero).
\end{eqnarray*}$$
2. We have
$$\begin{eqnarray*}
 &   & \npower(a,\next(\zero)) \\
 & = & \simprec{\varphi}{\mu}(\next(\zero),a) \\
 & = & \ntimes(a,\simprec{\varphi}{\mu}(\zero,a)) \\
 & = & \ntimes(a,\next(\zero)) \\
 & = & a.
\end{eqnarray*}$$
3. We have
$$\begin{eqnarray*}
 &   & \npower(\zero,\next(a)) \\
 & = & \simprec{\varphi}{\mu}(\next(a),\zero) \\
 & = & \ntimes(\zero,\npower(a,\zero)) \\
 & = & \zero.
\end{eqnarray*}$$
4. We proceed by induction on $a$. For the base case, we have $\npower(\next(\zero),\zero) = \next(\zero)$ by (1). For the inductive step, suppose $\npower(\next(\zero),a) = \next(\zero)$. Now
$$\begin{eqnarray*}
 &   & \npower(\next(\zero),\next(a)) \\
 & = & \simprec{\varphi}{\mu}(\next(a),\next(\zero)) \\
 & = & \ntimes(\next(\zero),\simprec{\varphi}{\mu}(a,\next(\zero))) \\
 & = & \ntimes(\next(\zero),\npower(\next(\zero),a)) \\
 & = & \npower(\next(\zero),a) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And interaction with $\nplus$ and $\ntimes$.

<div class="result">
<div class="theorem">
Let $a,b,c \in \nats$. Then we have the following.

1. $\npower(a,\next(b)) = \ntimes(a,\npower(a,b))$.
2. $\npower(a,\nplus(b,c)) = \ntimes(\npower(a,b),\npower(a,c))$.
3. $\npower(a,\ntimes(b,c)) = \npower(\npower(a,b),c)$.
4. $\npower(\ntimes(a,b),c) = \ntimes(\npower(a,c),\npower(b,c))$.
</div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \npower(a,\next(b)) \\
 & = & \simprec{\varphi}{\mu}(\next(b),a) \\
 & = & \ntimes(a,\simprec{\varphi}{\mu}(b,a)) \\
 & = & \ntimes(a,\npower(a,b))
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $c$. For the base case $c = \zero$, note that
$$\begin{eqnarray*}
 &   & \npower(a,\nplus(b,c)) \\
 & = & \npower(a,\nplus(b,\zero)) \\
 & = & \npower(a,b) \\
 & = & \ntimes(\npower(a,b),\next(\zero)) \\
 & = & \ntimes(\npower(a,b),\npower(a,\zero)) \\
 & = & \ntimes(\npower(a,b),\npower(a,c)).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $c \in \nats$. Now
$$\begin{eqnarray*}
 &   & \npower(a,\nplus(b,\next(c))) \\
 & = & \npower(a,\next(\nplus(b,c))) \\
 & = & \ntimes(a,\npower(a,\nplus(b,c))) \\
 & = & \ntimes(a,\ntimes(\npower(a,b),\npower(a,c))) \\
 & = & \ntimes(\npower(a,b),\ntimes(a,\npower(a,c))) \\
 & = & \ntimes(\npower(a,b),\npower(a,\next(c)))
\end{eqnarray*}$$
as claimed.
3. We proceed by induction on $c$. For the base case $c = \zero$, note that
$$\begin{eqnarray*}
 &   & \npower(a,\ntimes(b,c)) \\
 & = & \npower(a,\ntimes(b,\zero)) \\
 & = & \npower(a,\zero) \\
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
4. We proceed by induction on $c$. For the base case, we have
$$\begin{eqnarray*}
 &   & \npower(\ntimes(a,b),c) \\
 & = & \npower(\ntimes(a,b),\zero) \\
 & = & \next(\zero) \\
 & = & \ntimes(\next(\zero),\next(\zero)) \\
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
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``power``:

> power :: (Natural t) => t -> t -> t
> power a b = simpleRec phi mu b a
>   where
>     phi _     = next zero
>     mu  _ a b = times b a

Property tests:

> -- power(a,0) == 1
> _test_power_zero_right :: (Natural t) => t -> t -> Bool
> _test_power_zero_right _ a =
>   (power a zero) == (next zero)
> 
> 
> -- power(a,1) == a
> _test_power_one_right :: (Natural t) => t -> t -> Bool
> _test_power_one_right _ a =
>   (power a (next zero)) == a
> 
> 
> -- power(a,0) == 1
> _test_power_zero_left :: (Natural t) => t -> t -> Bool
> _test_power_zero_left _ a =
>   (power zero (next a)) == zero
> 
> 
> -- power(a,plus(b,c)) == times(power(a,b),power(a,c))
> _test_power_plus_right :: (Natural t) => t -> t -> t -> t -> Bool
> _test_power_plus_right _ a b c =
>   (power a (plus b c)) == times (power a b) (power a c)
> 
> 
> -- power(a,times(b,c)) == power(power(a,b),c)
> _test_power_times_right :: (Natural t) => t -> t -> t -> t -> Bool
> _test_power_times_right _ a b c =
>   (power a (times b c)) == power (power a b) c
> 
> 
> -- power(times(a,b),c) == times(power(a,c),power(b,c))
> _test_power_times_left :: (Natural t) => t -> t -> t -> t -> Bool
> _test_power_times_left _ a b c =
>   (power (times a b) c) == times (power a c) (power b c)

And the suite:

> -- run all tests for prime
> _test_power :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_power t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_power_zero_right t)
>   , quickCheckWith args (_test_power_one_right t)
>   , quickCheckWith args (_test_power_zero_left t)
>   , quickCheckWith args (_test_power_plus_right t)
>   , quickCheckWith args (_test_power_times_right t)
>   , quickCheckWith args (_test_power_times_left t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }