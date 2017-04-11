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

Next, we need a couple of technical lemmas. First one about remainders:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ with $\nleq(b,a)$, and suppose $b = \next(m)$. Then we have $$\nleq(\nplus(\nplus(b,\nrem(a,b))),\nplus(a,m)).$$
</div>

<div class="proof"><p>
Say $a = \nplus(b,k)$. There are two possibilities for $k$; either $k = \zero$ or $k = \next(u)$ for some $u$. Suppose first that $k = \zero$. In this case we have $\nrem(a,b) = \zero$, so that $b = \nplus(b,\nrem(a,b))$ and $\nplus(b,m) = \nplus(a,b)$. Thus $$\nleq(b,\nplus(a,m))$$ as claimed.

Suppose instead that $k = \next(u)$. By the division algorithm, we have $b = \nplus(\nrem(a,b),h)$ for some $h$. Now
$$\begin{eqnarray*}
 &   & \nplus(a,m) \\
 & = & \nplus(\nplus(b,k),m) \\
 & = & \nplus(\nplus(b,\next(u)),m) \\
 & = & \nplus(\nplus(b,u),\next(m)) \\
 & = & \nplus(\nplus(b,u),b) \\
 & = & \nplus(\nplus(b,u),\nplus(\nrem(a,b),h)) \\
 & = & \nplus(\nplus(b,\nrem(a,b)),\nplus(u,h)).
\end{eqnarray*}$$
In particular, we have $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,m))$$ as claimed.
</p></div>
</div>

Now a technical lemma about the guts of $\ngcd$:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ with $\nleq(b,a)$. Then for all $c \in \nats$, we have $$\Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\nplus(a,b),(a,b)).$$
</div>

<div class="proof"><p>
Let $A = \{(a,b) \in \nats \times \nats \mid \nleq(b,a)\}$, and define $B \subseteq A$ by $$B = \{(a,b) \in A \mid \forall c \in \nats, \Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\nplus(a,b),(a,b))\}.$$ Now define $f : A \rightarrow \nats$ by $f(a,b) = b$. We will show that $B = A$ by strong induction on $f$.

For the base case, suppose we have $(a,b) \in A$ such that $\zero = f(a,b) = b$. Note first that $$\Theta(\nplus(a,b),(a,b)) = \ngcd(a,b) = a.$$ Now there are two possibilities for $\nplus(\nplus(a,b),c)$. If $\nplus(\nplus(a,b),c) = \zero$, then we have $a = c = \zero$. In this case we have $$\Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\zero,(a,b)) = b = \zero = a$$ as claimed. If instead we have $\nplus(\nplus(a,b),c) = \next(d)$ for some $d$, then we have
$$\begin{eqnarray*}
 &   & \Theta(\nplus(\nplus(a,b),c),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & a
\end{eqnarray*}$$
(since $b = \zero$) as claimed. In either case, we have $(a,b) \in B$.

Now for the inductive step, suppose we have $n \in \nats$ such that $k \in B$ whenever $\nleq(k,n)$. Suppose now that $(a,b) \in A$ such that $b = f(a,b) = \next(n)$. We consider two cases: either $n = \zero$ or $n = \next(m)$ for some $m$.

Suppose $n = \zero$; then $b = \next(\zero)$. In this case we have $\nplus(a,b) = \next(d)$ for some $d$ and $\nplus(\nplus(a,b),c) = \next(e)$ for some $e$. Now
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & \next(\zero) \\
 & = & \psi(e,(a,b)) \\
 & = & \Theta(\next(e),(a,b)) \\
 & = & \Theta(\nplus(\nplus(a,b),c),(a,b))
\end{eqnarray*}$$
as claimed.

Suppose instead that $n = \next(m)$. By the previous lemma, note that $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,n)),$$ and thus we have $$\nplus(a,n) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Note also that $\nleq(\nrem(a,b),n)$ by the division algorithm; in particular, we have $(b,\nrem(a,b)) \in B$ by the induction hypothesis. Now we have
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(\nplus(a,n)),(a,b)) \\
 & = & \Theta(\nplus(a,n),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),u),(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),\nplus(u,c)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,n),c),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,b),c),(a,b))
\end{eqnarray*}$$
as claimed. Thus $(a,b) \in B$, and by strong induction we have $B = A$.
</p></div>
</div>

And a corollary:

<div class="result">
<div class="corollary">
Let $a,b \in \nats$. Then $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$.
</div>

<div class="proof"><p>
Suppose first that $\nleq(b,a)$. We consider three possibilities for $b$: either $b = \zero$, $b = \next(\zero)$, or $b = \next(\next(m))$ for some $m$.

If $b = \zero$, then we have $\nrem(a,b) = a$. In this case $$\ngcd(a,b) = \ngcd(b,a) = \ngcd(b,\nrem(a,b))$$ as claimed.

If $b = \next(\zero)$, then we have $\nrem(a,b) = \zero$ and $\nplus(a,b) = \next(d)$ for some $d$. Now
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & \next(\zero) \\
 & = & b \\
 & = & \ngcd(b,\zero) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.

Finally, suppose $b = \next(\next(m))$. Again we have $$\nplus(a,\next(m)) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Now
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(\nplus(a,\next(m))),(a,b)) \\
 & = & \Theta(\nplus(a,\next(m)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),u),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b))) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.

Suppose instead that $\nleq(b,a)$ is false; then $\nleq(a,b)$ is true and $a \neq b$. In particular $b \neq \zero$; say $b = \next(m)$. In this case $\nrem(b,a) = a$. So we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \ngcd(b,a) \\
 & = & \ngcd(b,\nrem(a,b)) \\
\end{eqnarray*}$$
as claimed.
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
