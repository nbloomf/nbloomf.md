---
title: Is Prime
author: nbloomf
date: 2017-04-20
tags: arithmetic-made-difficult, literate-haskell
---

> module IsPrime
>   ( isPrime, _test_isPrime
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

Today we'll nail down what it means for a natural number to be *prime*. Typically this is done by saying something like "a natural number other than 0 or 1 is prime if it is not divisible by any natural number besides itself and 1" and from there, arguing that this property can be checked using trial division. As is typical in this series, we will turn this around -- *defining* primes to be those numbers which are detected by trial division (i.e. an algorithm) and then proving that such numbers have the divisibility properties we expect.

In fact we'll do a little more: instead of simply using trial division to detect whether a natural number $n$ is prime, we can use it to find the smallest divisor of $n$. If the smallest divisor is $n$ itself, then $n$ is prime. To make this work we have to define "smallest divisor" in such a way that the trivial divisor $\next(\zero)$ is excluded. We will call this function that finds the smallest divisor $\nmindiv$, and intuitively it should have the signature $\nats \rightarrow \nats$.

<div class="result">
<div class="defn"><p>
Define $\varphi : \nats \rightarrow \nats \rightarrow \bool$ by $$\varphi(a)(b) = a,$$ $\beta : \nats \rightarrow \nats \times \nats \rightarrow \bool$ by $$\beta(a)(k,b) = \ndiv(b,a),$$ $\psi : \nats \rightarrow \nats \times \nats \rightarrow \nats$ by $$\psi(a)(k,b) = b,$$ and $\omega : \nats \rightarrow \nats \times \nats \rightarrow \nats$ by $$\omega(a)(k,b) = \next(b).$$ Now define $\nmindiv : \nats \rightarrow \bool$ by $$\nmindiv(a) = \bailrec{\varphi(a)}{\beta(a)}{\psi(a)}{\omega(a)}(a,\next(\next(a))).$$
</p></div>
</div>

For brevity we will define $\Theta : \nats \times \nats \rightarrow \nats$ by $$\Theta = \bailrec{\varphi(a)}{\beta(a)}{\psi(a)}{\omega(a)}$$ as in the definition of $\nmindiv$.

<div class="result">
<div class="lemma">
Let $a \in \nats$. Suppose $t \in \nats$ has the property that $t \neq \zero$, $t \neq \next(\zero)$, and $\ndiv(t,a) = \btrue$, and if $k \in \nats$ with $\nleq(k,t)$, $k \neq \zero$, $k \neq \next(\zero)$, and $k \neq t$, then $\ndiv(k,a) = \bfalse$.

Then for all $u \in \nats$, if $$\nleq(\next(\next(\next(u))),t) = \btrue$$ then $$\Theta(a,\next(\next(\zero))) = \Theta(\nminus(a,u),\next(\next(u))).$$
</div>

<div class="proof"><p>
We proceed by induction on $u$. For the base case $u = \zero$, the implication is either vacuous (if $\nleq(\next(\next(\next(\zero))),t)$ is false) or trivial (otherwise, since in this case we have $\nminus(a,\zero) = a$).

For the inductive step, suppose the implication holds for some $u \in \nats$. Suppose further that $$\nleq(\next(\next(\next(\next(u)))),t).$$ Now $$\nleq(\next(\next(\next(u))),t).$$ Say $t = \nplus(\next(u),h)$ and $t = \nplus(u,k)$; then we have $k = \next(h)$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \Theta(a,\next(\next(\zero))) \\
 & = & \Theta(\nminus(a,u),\next(\next(u))) \\
 & = & \Theta(k,\next(\next(u))) \\
 & = & \Theta(\next(h),\next(\next(u))) \\
 & = & Q
\end{eqnarray*}$$
Note that $\next(\next(u))$ is not $\zero$, $\next(\zero)$, or $t$. Thus $\ndiv(\next(\next(u)),a) = \bfalse$, and we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \Theta(h,\next(\next(\next(u)))) \\
 & = & \Theta(\nminus(a,\next(u)),\next(\next(\next(u))))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

We can show that $\nmindiv(a)$ is the smallest divisor of $a$ in an appropriate sense.

<div class="result">
<div class="thm"><p>
Let $a \in \nats$ with $a \neq \zero$ and $a \neq \next(\zero)$. Then we have the following.

1. $\nmindiv(a) \neq \zero$ and $\nmindiv(a) \neq \next(\zero)$ and $\ndiv(\nmindiv(a),a)$.
2. If $k \neq \zero$ and $k \neq \next(\zero)$ and $\ndiv(k,a)$, then $\nleq(\nmindiv(a),k)$.
</p></div>

<div class="proof"><p>
Let $a \in \nats$ with $a \neq \zero$ and $a \neq \next(\zero)$. Now define a set $D(a) \subseteq \nats$ by $$D(a) = \{ k \in \nats \mid k \neq \zero, k \neq \next(\zero), \ndiv(k,a) \}.$$ Now $D(a)$ is not empty, since $a \in D(a)$. By the Well-Ordering Property, then, $D(a)$ has a least element; we call this element $\mu_a$. Certainly $\mu_a$ satisfies conditions (1) and (2); thus it suffices to show that $\nmindiv(a) = \mu_a$. We consider two possibilities: either $\mu_a = \next(\next(\zero))$ or $\mu_a = \next(\next(\next(m)))$ for some $m$. (Note that $\mu_a$ is not $\zero$ or $\next(\zero)$ by definition.

First suppose $\mu_a = \next(\next(\zero))$. Note that $a = \next(b)$ for some $b$ (since $a \neq \zero$). Now
$$\begin{eqnarray*}
 &   & \nmindiv(a) \\
 & = & \Theta(a,\next(\next(\zero))) \\
 & = & \Theta(\next(b),\next(\next(\zero))) \\
 & = & \next(\next(\zero)) \\
 & = & \mu_a
\end{eqnarray*}$$
since $\ndiv(\next(\next(\zero)),a)$. Now suppose $\mu_a = \next(\next(\next(m)))$. Note that $\nminus(a,m) = \next(\next(q))$. By the lemma, we have
$$\begin{eqnarray*}
 &   & \nmindiv(a) \\
 & = & \Theta(a,\next(\next(\zero))) \\
 & = & \Theta(\nminus(a,m),\next(\next(m)))) \\
 & = & \Theta(\next(\next(q)),\next(\next(m))) \\
 & = & R. \\
\end{eqnarray*}$$
Now $\ndiv(\next(\next(m)),a) = \bfalse$, since $\next(\next(m))$ is not $\zero$, $\next(\zero)$, or $\mu_a$, and $\mu_a$ is minimal in $D(a)$. Thus we have
$$\begin{eqnarray*}
 &   & R \\
 & = & \Theta(\next(q),\next(\next(\next(m)))) \\
 & = & \next(\next(\next(m))) \\
 & = & \mu_a
\end{eqnarray*}$$
as claimed.
</p></div>
</div>



<div class="result">
<div class="thm">
Let $a \in \nats$. Then the following are equivalent.

1. $\nisprime(a) = \btrue$.
2. $a \neq \zero$ and $a \neq \next(\zero)$, and there exists $b \in \nats$ such that $b \neq a$ and $b \neq \next(\zero)$ and $\ndiv(b,a)$.
3. $a \neq \zero$ and $a \neq \next(\zero)$, and if $u,v \in \nats$ such that $a = \ntimes(u,v)$, then $(u,v)$ is either $(\next(\zero),a)$ or $(a,\next(\zero))$.
4. $a \neq \zero$ and $a \neq \next(\zero)$, and if $u,v \in \nats$ such that $\ndiv(a,\ntimes(u,v))$, then either $\ndiv(a,u)$ or $\ndiv(a,v)$.
</div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``mindiv`` and ``prime``:

> mindiv :: (Natural t) => t -> t
> mindiv a = theta a (next (next zero))
>   where
>     theta = bailoutRec (phi a) (beta a) (psi a) (omega a)
> 
>     phi   a   _ = a
>     beta  a _ b = div b a
>     psi   _ _ b = b
>     omega a _ b = next b
> 
> 
> prime :: (Natural t) => t -> Bool
> prime a
>   | leq a (next zero) = False
>   | otherwise         = a == mindiv a

Property tests for ``isPrime``:

> -- prime(next(next(zero))) == true
> --_test_prime_case :: (Natural t) => t -> Bool
> --_test_prime_case a = isPrime a == True

And the suite:

> -- run all tests for prime
> _test_prime :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_prime t maxSize numCases = sequence_
>   [ --quickCheckWith args (_test_lcm_zero t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
