---
title: Least Common Multiple
author: nbloomf
date: 2017-04-12
tags: arithmetic-made-difficult, literate-haskell
---

> module LeastCommonMultiple
>   ( lcm, _test_lcm
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
> 
> import Test.QuickCheck

Recall the following property of $\nmax$: if $\nleq(c,a)$ and $\nleq(c,b)$, then $\nleq(c,\nmax(a,b))$. This statement fell out of the definition of $\nmax$ without much fuss, and may seem anticlimactic. But compare it to this analogous statement about $\ngcd$: if $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$. Now $\nmax$ and $\ngcd$ seem to play very similar roles. Where $\nleq$ is a kind of "additive order" on $\nats$ and $\nmax$ gives an additive ceiling to $a$ and $b$, $\ndiv$ is a kind of "multiplicative order" and $\ngcd$ gives a multiplicative ceiling to $a$ and $b$. When an analogy this strong holds between two concepts in mathematics, it is frequently useful to see how far the analogy goes. To that end, today we will define the multiplicative counterpart to $\nmin$.

We don't need recursion for this.

<div class="result">
<div class="defn"><p>
Define $\nlcm : \nats \times \nats \rightarrow \nats$ by $$\nlcm(a,b) = \nquo(\ntimes(a,b),\ngcd(a,b)).$$
</p></div>
</div>

woo special cases!

<div class="result">
<div class="lemma">
For all $a \in \nats$ we have the following.

1. $\nlcm(a,\zero) = \zero$.
2. $\nlcm(a,\next(\zero)) = a$.
</div>

<div class="proof"></p>
1. Note that
$$\begin{eqnarray*}
 &   & \nlcm(a,\zero) \\
 & = & \nquo(\ntimes(a,\zero),\ngcd(a,\zero)) \\
 & = & \nquo(\zero,a) \\
 & = & \zero.
\end{eqnarray*}$$
2. Note that
$$\begin{eqnarray*}
 &   & \nlcm(a,\next(\zero)) \\
 & = & \nquo(\ntimes(a,\next(\zero)),\ngcd(a,\next(\zero))) \\
 & = & \nquo(a,\next(\zero)) \\
 & = & a.
\end{eqnarray*}$$
</p></div>
</div>

As we might expect, $\nlcm$ enjoys many properties analogous to those of $\ngcd$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nlcm(a,a) = a$.
2. $\nlcm(a,b) = \nlcm(b,a)$.
</div>

<div class="proof"><p>
1. We consider two cases: $a = \zero$ and $a \neq \zero$. If $a = \zero$, we have
$$\begin{eqnarray*}
 &   & \nlcm(a,a) \\
 & = & \nquo(\ntimes(a,a),\ngcd(a,a)) \\
 & = & \nquo(\zero,\zero) \\
 & = & \zero \\
 & = & a
\end{eqnarray*}$$
as claimed. If $a \neq \zero$, say $a = \next(t)$, then we have
$$\begin{eqnarray*}
 &   & \nlcm(a,a) \\
 & = & \nquo(\ntimes(a,a),\ngcd(a,a)) \\
 & = & \nquo(\ntimes(a,a),a) \\
 & = & a
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \nlcm(a,b) \\
 & = & \nquo(\ntimes(a,b),\ngcd(a,b)) \\
 & = & \nquo(\ntimes(b,a),\ngcd(b,a)) \\
 & = & \nlcm(b,a)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And the universal property:

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\ndiv(a,\nlcm(a,b))$ and $\ndiv(b,\nlcm(a,b))$.
2. If $\ndiv(a,c)$ and $\ndiv(b,c)$, then $\ndiv(\nlcm(a,b),c)$.
</div>

<div class="proof"><p>
1. We consider two cases: $\ngcd(a,b) = \zero$ and $\ngcd(a,b) \neq \zero$. If $\ngcd(a,b) = \zero$, then we have $a = b = \zero$. Now
$$\begin{eqnarray*}
 &   & \nlcm(\zero,\zero) \\
 & = & \nquo(\ntimes(\zero,\zero),\ngcd(\zero,\zero)) \\
 & = & \nquo(\zero,\zero) \\
 & = & \zero
\end{eqnarray*}$$
and $\ndiv(\zero,\zero)$ as needed. Suppose instead that $\ngcd(a,b) \neq \zero$. Say $b = \ntimes(k,\ngcd(a,b))$. Now
$$\begin{eqnarray*}
 &   & \nlcm(a,b) \\
 & = & \nquo(\ntimes(a,b),\ngcd(a,b)) \\
 & = & \nquo(\ntimes(\ntimes(a,k),\ngcd(a,b)),\ngcd(a,b)) \\
 & = & \ntimes(a,k),
\end{eqnarray*}$$
so that $\ndiv(a,\nlcm(a,b))$. A similar argument shows that $\ndiv(b,\nlcm(a,b))$ as claimed.
2. Suppose we have $\ndiv(a,c)$ and $\ndiv(b,c)$. (@@@)
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``lcm``:

> lcm :: (Natural t) => t -> t -> t
> lcm a b = quo (times a b) (gcd a b)

Property tests for ``lcm``:

> -- lcm(a,0) == 0 and lcm(0,a) == 0
> _test_lcm_zero :: (Natural t) => t -> t -> Bool
> _test_lcm_zero _ a = and
>   [ zero == lcm a zero
>   , zero == lcm zero a
>   ]
> 
> 
> -- lcm(a,next(0)) == a and lcm(next(0),a) == a
> _test_lcm_one :: (Natural t) => t -> t -> Bool
> _test_lcm_one _ a = and
>   [ a == lcm a (next zero)
>   , a == lcm (next zero) a
>   ]
> 
> 
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
> 
> 
> -- lcm(a,b) == lcm(b,a)
> _test_lcm_commutative :: (Natural t) => t -> t -> t -> Bool
> _test_lcm_commutative _ a b =
>   (lcm a b) == (lcm b a)

And the suite:

> -- run all tests for lcm
> _test_lcm :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_lcm t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_lcm_zero t)
>   , quickCheckWith args (_test_lcm_one t)
>   , quickCheckWith args (_test_lcm_div_args t)
>   , quickCheckWith args (_test_lcm_idempotent t)
>   , quickCheckWith args (_test_lcm_commutative t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
