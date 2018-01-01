---
title: Is Prime
author: nbloomf
date: 2017-04-13
tags: arithmetic-made-difficult, literate-haskell
slug: isprime
---

> module IsPrime
>   ( mindiv, prime, _test_prime, main_prime
>   ) where
> 
> import Prelude ()
> import Booleans
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> import GreatestCommonDivisor
> import CoprimeTo
> import LeastCommonMultiple
> import FindSmallest

Today we'll nail down what it means for a natural number to be *prime*. Typically this is done by saying something like "a natural number other than 0 or 1 is prime if it is not divisible by any natural number besides itself and 1" and from there, arguing that this property can be checked using trial division. As is typical in this series, we will turn this around -- *defining* primes to be those numbers which are detected by trial division (i.e. an algorithm) and then proving that such numbers have the divisibility properties we expect.

In fact we'll do a little more: instead of simply using trial division to detect whether a natural number $n$ is prime, we can use it to find the smallest divisor of $n$. If the smallest divisor is $n$ itself, then $n$ is prime. To make this work we have to define "smallest divisor" in such a way that the trivial divisor $\next(\zero)$ is excluded. We will call this function that finds the smallest divisor $\nmindiv$, and intuitively it should have the signature $\nats \rightarrow \nats$.

<div class="result">
<div class="defn"><p>
Define $\sigma : \nats \rightarrow \bool^{\nats}$ by $$\sigma(a)(b) = \div(b,a),$$ and define $\varphi : \nats \rightarrow 1 + \nats$ piecewise by
$$\nmindiv(n) = \left\{\begin{array}{ll}
 \rgt(\zero) & \mathrm{if}\ n = \zero \\
 \rgt(\next(\zero)) & \mathrm{if}\ n = \next(\zero) \\
 \findsmallest{\sigma(n)}(m,\next(\next(\zero))) & \mathrm{if}\ n = \next(\next(m)).
\end{array}\right.$$
Now define $\nmindiv : \nats \rightarrow \nats$ by $$\nmindiv(n) = \either(\const(n),\id)(\varphi(n)).$$

In Haskell:

> mindiv :: (Natural n, Equal n) => n -> n
> mindiv n = either (const n) id (phi n)
>   where
>     phi n = case natShape n of
>       Zero -> rgt zero
>       Next k -> case natShape k of
>         Zero -> rgt (next zero)
>         Next m -> findSmallest (sigma n) m (next (next zero))
> 
>     sigma n a = div a n

</p></div>
</div>

Almost by definition, $\nmindiv(a)$ is the smallest divisor of $a$ in a precise sense.

<div class="result">
<div class="thm"><p>
Let $a \in \nats$ with $\nleq(\next(\next(\zero)),a)$. Then we have the following.

1. $\nleq(\next(\next(\zero)),\nmindiv(a))$ and $\ndiv(\nmindiv(a),a)$.
2. If $\nleq(\next(\next(\zero)),k)$ and $\ndiv(k,a)$, then $\nleq(\nmindiv(a),k)$.
</p></div>

<div class="proof"><p>
If $a = \next(\next(m))$ for some $m$, we have
$$\begin{eqnarray*}
 &   & \nmindiv(a) \\
 & = & \nmindiv(\next(\next(m))) \\
 & = & \either(\const(a),\id)(\findsmallest(\sigma(a))(m,\next(\next(\zero)))).
\end{eqnarray*}$$
We have two possibilities for $\findsmallest(\sigma(a))(m,\next(\next(\zero))) = Q$.

Suppose $Q = \rgt(t)$; then we have
$$\begin{eqnarray*}
 &   & \either(\const(a),\id)(Q) \\
 & = & \either(\const(a),\id)(\rgt(t)) \\
 & = & \id(t) \\
 & = & t.
\end{eqnarray*}$$
By the properties of $\findsmallest$ we have $\nleq(\next(\next(\zero)),t)$ and $\nleq(t,\next(m))$ (so $t \neq \zero$ and $t \neq \next(\zero)$) and $\ndiv(t,a)$, and moreover if $\nleq(\next(\next(\zero)),k)$ and $\nleq(k,\next(m))$ and $\ndiv(k,a)$ then $\nleq(t,k)$ as claimed.

Suppose instead that $Q = \lft(\ast)$; then we have
$$\begin{eqnarray*}
 &   & \either(\const(a),\id)(Q) \\
 & = & \either(\const(a),\id)(\lft(\ast)) \\
 & = & \const(a)(\ast) \\
 & = & a. 
\end{eqnarray*}$$
Again by the properties of $\findsmallest$, there does not exist $k$ such that $\nleq(\next(\next(\zero)),k)$ and $\nleq(k,\next(m))$ and $\ndiv(k,a)$ as claimed.
</p></div>

<div class="test"><p>

> _test_mindiv_div :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_mindiv_div _ =
>   testName "if leq(next(next(zero)),a) then leq(next(next(zero)),mindiv(a)) and div(mindiv(a),a)" $
>   \a -> if leq (next (next zero)) a
>     then and (leq (next (next zero)) (mindiv a)) (div (mindiv a) a)
>     else True
> 
> 
> _test_mindiv_min :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_mindiv_min _ =
>   testName "if leq(next(next(zero)),k) and div(k,a) then leq(mindiv(a),k)" $
>   \a k -> if and (leq (next (next zero)) k) (div k a)
>     then leq (mindiv a) k
>     else True

</p></div>
</div>

Now we define a boolean function $\nisprime$ as follows.

<div class="result">
<div class="defn"><p>
Define $\nisprime : \nats \rightarrow \bool$ by $$\nisprime(a) = \left\{ \begin{array}{ll} \bfalse & \mathrm{if} a = \zero\ \mathrm{or}\ a = \next(\zero) \\ \nequal(a,\nmindiv(a)) & \mathrm{otherwise}. \end{array} \right.$$

In Haskell:

> prime :: (Natural n, Equal n) => n -> Bool
> prime a = if leq a (next zero)
>   then False
>   else eq a (mindiv a)

</p></div>
</div>

It is straightforward to show that $\nisprime$ is equivalent to the usual definition.

<div class="result">
<div class="thm">
Let $a \in \nats$. Then the following are equivalent.

1. $\nisprime(a) = \btrue$.
2. $a \neq \zero$ and $a \neq \next(\zero)$, and if $u,v \in \nats$ such that $a = \ntimes(u,v)$, then $(u,v)$ is either $(\next(\zero),a)$ or $(a,\next(\zero))$.
3. $a \neq \zero$ and $a \neq \next(\zero)$, and if $u,v \in \nats$ such that $\ndiv(a,\ntimes(u,v))$, then either $\ndiv(a,u)$ or $\ndiv(a,v)$.
</div>

<div class="proof"><p>
$(1)$ implies $(2)$: Suppose $\nisprime(a) = \btrue$. Certainly $a \neq \zero$ and $a \neq \next(\zero)$ (by definition), and we have $a = \nmindiv(a)$. Suppose now that $a = \ntimes(u,v)$; we consider three cases for $u$. If $u = \zero$ we have $a = \zero$, a contradiction. If $u = \next(\zero)$, then $v = a$. If $a \neq \zero$ and $a \neq \next(\zero)$, we have $\ndiv(u,a)$, so that $\nleq(\nmindiv(a),u)$; thus $\nleq(a,u)$. But also $\nleq(u,a)$, so that $u = a$, and thus $v = \next(\zero)$ as claimed.

$(2)$ implies $(3)$: Of course $a \neq \zero$ and $a \neq \next(\zero)$. Say $\ndiv(a,\ntimes(u,v))$, and consider $\ngcd(a,u)$. In particular, we have $a = \ntimes(k,\ngcd(a,u))$ for some $k$. There are two possibilities: if $\ngcd(a,u) = a$, then $\ndiv(a,u)$, and if $\ngcd(a,u) = \next(\zero)$, then $\ndiv(a,v)$ by Euclid's lemma.

$(3)$ implies $(1)$: It suffices to show that if $a \neq \zero$ and $a \neq \next(\zero)$ then $\nmindiv(a) = a$. To this end, let $d = \nmindiv(a)$ and write $a = \ntimes(\nmindiv(a),k)$. Suppose $\ndiv(a,k)$, with $k = \ntimes(a,w)$. Since $a \neq \zero$, by cancellation we have $\next(\zero) = \ntimes(\nmindiv(a),w)$, so that $\nmindiv(a) = \next(\zero)$, a contradiction. Thus $\ndiv(a,\nmindiv(a))$, so we have $a = \nmindiv(a)$ as needed.
</p></div>

<div class="test"><p>

(@@@)

</p></div>
</div>

Minimal divisors are prime.

<div class="result">
<div class="thm">
Let $a \in \nats$ with $a \neq \zero$ and $a \neq \next(\zero)$. Then $$\nisprime(\nmindiv(a)) = \btrue.$$
</div>

<div class="proof"><p>
Let $a \in \nats$ with $a \neq \zero$ and $a \neq \next(\zero)$, and let $d = \nmindiv(a)$. Suppose now that $d = \ntimes(u,v)$. Since $d \neq \zero$, we have $u \neq \zero$. If $u = \next(\zero)$, we have $v = d$. If $u \neq \next(\zero)$, we have $\ndiv(u,a)$ and thus $\nleq(d,u)$; but $\nleq(u,d)$, so that $d = u$ by antisymmetry and thus $v = \next(\zero)$. Thus $\nisprime(\nmindiv(a))$ as claimed.
</p></div>

<div class="test"><p>

> _test_prime_mindiv :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_prime_mindiv _ =
>   testName "if leq(next(next(zero)),a) then prime(mindiv(a)) == true" $
>   \a -> if leq (next (next zero)) a
>     then eq (prime (mindiv a)) True
>     else True

</p></div>
</div>

Primes interact with $\ngcd$ as expected.

<div class="result">
<div class="thm">
Let $p,a \in \nats$ with $\nisprime(p)$. Then $$\ngcd(a,p) = \left\{ \begin{array}{ll} p & \mathrm{if}\ \ndiv(p,a) \\ \next(\zero) & \mathrm{otherwise}. \end{array} \right.$$
</div>

<div class="proof"><p>
Let $d = \ngcd(a,p)$. Now $\ndiv(d,p)$, so that either $d = \next(\zero)$ or $d = p$. If $\ndiv(p,a) = \bfalse$, we thus have $d = \next(\zero)$.
</p></div>

<div class="test"><p>

(@@@)

</p></div>
</div>


Testing
-------

Suite:

> _test_prime ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_prime n maxSize numCases = do
>   testLabel ("mindiv & prime: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_mindiv_div n)
>   runTest args (_test_mindiv_min n)
>   runTest args (_test_prime_mindiv n)

Main:

> main_prime :: IO ()
> main_prime = do
>   _test_prime (zero :: Unary) 40 100
