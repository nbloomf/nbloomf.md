---
title: Greatest Common Divisor
author: nbloomf
date: 2017-04-10
tags: arithmetic-made-difficult, literate-haskell
---

> module GreatestCommonDivisor
>   ( gcd, lcm, _test_gcd_lcm
>   ) where
>
> import Prelude hiding (max, min, div, rem, gcd, lcm)
>
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import MaxAndMin
> import DivisionAlgorithm
> import Divides
> 
> import Test.QuickCheck

Today we'll define the greatest common divisor of two natural numbers. The usual way to do this (in books I've seen) is to define what it means to say that $d$ is a greatest common divisor of $a$ and $b$, then show (possibly nonconstructively) that any two $a$ and $b$ have a greatest common divisor, and finally establish the Euclidean algorithm that actually computes GCDs. We will work backwards: first *defining* the GCD of two natural numbers using the punchline of the Euclidean algorithm and then proving that the output of this function acts like the GCD.

We'll do this using bailout recursion. This definition will be trickier to work with than the others we've seen so far because the "countdown timer" is just for show -- we expect it to actually reach zero only in one special case. For this reason reasoning about the recursive step is awkward.

<div class="result">
<div class="defn"><p>
Define maps $\varphi : \nats \times \nats \rightarrow \nats$ by $$\varphi(a,b) = b,$$ then $\beta : \nats \times (\nats \times \nats) \rightarrow \bool$ by $$\beta(k,(a,b)) = \nleq(b,\next(\zero)),$$ then $\psi : \nats \times (\nats \times \nats) \rightarrow \nats$ by $$\psi(k,(a,b)) = \left\{\begin{array}{ll} a & \mathrm{if}\ b = \zero \\ \next(\zero) & \mathrm{otherwise}, \end{array}\right.$$ and $\omega : \nats \times (\nats \times \nats) \rightarrow \nats \times \nats$ by $$\omega(k,(a,b)) = (b, \nrem(a,b)).$$ We then define a map $\ngcd : \nats \times \nats \rightarrow \nats$ by $$\ngcd(a,b) = \bailrec{\varphi}{\beta}{\psi}{\omega}(\nplus(a,b))(\nmax(a,b),\nmin(a,b)).$$
</p></div>
</div>

For brevity's sake, we let $\Theta = \bailrec{\varphi}{\beta}{\psi}{\omega}$ for the rest of this post. Now the definition of $\ngcd$ makes commutativity immediate.

<div class="result">
<div class="lemma">
For all $a,b \in \nats$, we have $\ngcd(a,b) = \ngcd(b,a)$.
</div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(\nplus(a,b),(\nmax(a,b),\nmin(a,b)) \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(\nplus(b,a),(\nmax(b,a),\nmin(b,a)) \\
 & = & \ngcd(b,a)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And now a special case.

<div class="result">
<div class="lemma">
For all $a \in \nats$, we have $\ngcd(a,\zero) = \ngcd(\zero,a) = a$.
</div>

<div class="proof"><p>
It suffices to show that $\ngcd(a,\zero) = a$. If $a = \zero$, note that
$$\begin{eqnarray*}
 &   & \ngcd(\zero,\zero) \\
 & = & \Theta(\zero,(\zero,\zero)) \\
 & = & \varphi(\zero,\zero) \\
 & = & \zero \\
 & = & a
\end{eqnarray*}$$
as needed. If $a = \next(d)$, we have
$$\begin{eqnarray*}
 &   & \ngcd(a,\zero) \\
 & = & \Theta(\next(d),(a,\zero)) \\
 & = & \psi(d,(a,\zero)) \\
 & = & a
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Next, we need a technical lemma.

<div class="result">
<div class="lemma">
(@@@)
</div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``gcd`` and ``lcm``:

> gcd :: (Natural t) => t -> t -> t
> gcd a b = (bailoutRec phi beta psi omega) (plus a b) (max a b, min a b)
>   where
>     phi (_,b) = b
>     beta _ (_,b) = leq b (next zero)
>     omega _ (a,b) = (b, rem a b)
> 
>     psi _ (a,b) = if b == zero
>       then a
>       else next zero
> 
> 
> lcm :: (Natural t) => t -> t -> t
> lcm a b = quo (times a b) (gcd a b)

Property tests for ``gcd``:

> -- gcd(a,b) == gcd(b,a)
> _test_gcd_commutative :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_commutative _ a b =
>   (gcd a b) == (gcd b a)
> 
> 
> -- gcd(a,0) == a and gcd(0,a) == a
> _test_gcd_zero :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_zero _ a b = and
>   [ a == gcd a zero
>   , a == gcd zero a
>   ]
> 
> 
> -- div(gcd(a,b),a) and div(gcd(a,b),b)
> _test_gcd_div_args :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_div_args _ a b = and
>   [ div (gcd a b) a
>   , div (gcd a b) b
>   ]
> 
> 
> -- gcd(a,a) = a
> _test_gcd_idempotent :: (Natural t) => t -> t -> Bool
> _test_gcd_idempotent _ a =
>   (gcd a a) == a

Property tests for ``lcm``:

> -- div(a,lcm(a,b)) and div(b,lcm(a,b))
> _test_lcm_div_args :: (Natural t) => t -> t -> t -> Bool
> _test_lcm_div_args _ a b = and
>   [ div a (lcm a b)
>   , div b (lcm a b)
>   ]
> 
> 
> -- lcm(a,a) = a
> _test_lcm_idempotent :: (Natural t) => t -> t -> Bool
> _test_lcm_idempotent _ a =
>   (lcm a a) == a

And the suite:

> -- run all tests for div
> _test_gcd_lcm :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_gcd_lcm t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_gcd_commutative t)
>   , quickCheckWith args (_test_gcd_zero t)
>   , quickCheckWith args (_test_gcd_div_args t)
>   , quickCheckWith args (_test_gcd_idempotent t)
> 
>   , quickCheckWith args (_test_lcm_div_args t)
>   , quickCheckWith args (_test_lcm_idempotent t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
