---
title: Divides
author: nbloomf
date: 2017-04-09
tags: arithmetic-made-difficult, literate-haskell
slug: div
---

> module Divides
>   ( div, _test_div, main_div
>   ) where
>
> import Prelude ()
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> import DivisionAlgorithm

With the division algorithm in hand we can define what it means for one natural number to divide another.

<div class="result">
<div class="defn"><p>
We define $\ndiv : \nats \times \nats \rightarrow \bool$ by $$\ndiv(a,b) = \iszero(\nrem(b,a)).$$

In Haskell:

> div :: (Natural n, Equal n) => n -> n -> Bool
> div a b = isZero (rem b a)

</p></div>
</div>

Now $\ndiv$ is to $\ntimes$ as $\nleq$ is to $\nplus$ as follows.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\ndiv(a,b) = \btrue$ if and only if there exists $c \in \nats$ such that $b = \ntimes(c,a)$.
</div>

<div class="proof"><p>
Suppose first that $\ndiv(a,b) = \btrue$. Letting $(q,r) = \ndivalg(b,a)$, we have $r = \zero$, so that $$b = \nplus(\ntimes(q,a),r) = \ntimes(q,a)$$ as claimed.

Conversely, suppose there is a natural number $c$ such that $b = \ntimes(c,a)$. If $a = \zero$, then in fact $b = \zero$, and we have $\nrem(b,a) = \zero$, so that $\ndiv(a,b)$. Suppose instead that $a = \next(d)$. Since $$b = \nplus(\ntimes(c,\next(d)),\zero)$$ and $$\nleq(\zero,\next(d)),$$ we have $$(c,\zero) = \ndivalg(b,a).$$ Thus $\nrem(b,a) = \zero$ as needed.
</p></div>
</div>

From here the usual properties of divisibility are straightforward. First, $\ndiv$ interacts with $\zero$ and $\next(\zero)$.

<div class="result">
<div class="thm">
Let $a \in \nats$. We have the following.

1. $\ndiv(a,\zero)$.
2. If $\ndiv(\zero,a)$, then $a = \zero$.
3. $\ndiv(\next(\zero),a)$.
4. If $\ndiv(a,\next(\zero))$, then $a = \next(\zero)$.
</div>

<div class="proof"><p>
1. Note that $\zero = \ntimes(\zero,a)$.
2. We have $c \in \nats$ such that $a = \ntimes(c,\zero) = \zero$.
3. Note that $a = \ntimes(a,\next(\zero))$.
4. We've seen that if $\ntimes(a,b) = \next(\zero)$ then $a = b = \next(\zero)$.
</p></div>

<div class="test"><p>

> _test_div_zero_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_div_zero_right _ =
>   testName "div(a,0) == true" $
>   \a -> eq (div a zero) True
> 
> 
> _test_div_zero_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_div_zero_left _ =
>   testName "if div(0,a) then eq(a,0)" $
>   \a -> if div zero a
>     then eq a zero
>     else True
> 
> 
> _test_div_one_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_div_one_left _ =
>   testName "div(next(0),a)" $
>   \a -> div (next zero) a
> 
> 
> _test_div_one_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_div_one_right _ =
>   testName "if div(a,next(0)) then eq(a,next(0))" $
>   \a -> if div a (next zero)
>     then eq a (next zero)
>     else True

</p></div>
</div>

And $\ndiv$ is reflexive, antisymmetric, and transitive.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. We have the following.

1. $\ndiv(a,a)$.
2. If $\ndiv(a,b)$ and $\ndiv(b,a)$, then $a = b$.
3. If $\ndiv(a,b)$ and $\ndiv(b,c)$, then $\ndiv(a,c)$.
</div>

<div class="proof"><p>
1. Note that $a = \ntimes(\next(\zero),a)$.
2. First suppose $a = \zero$. Since $\ndiv(a,b)$, we have $b = 0$ as needed. Now suppose $a = \next(d)$. We have $h,k \in \nats$ such that $a = \ntimes(h,b)$ and $b = \ntimes(k,a)$; now
$$\begin{eqnarray*}
 &   & \ntimes(\next(\zero),\next(d)) \\
 & = & \next(d) \\
 & = & b \\
 & = & \ntimes(\ntimes(h,k),b) \\
 & = & \ntimes(\ntimes(h,k),\next(d));
\end{eqnarray*}$$
so we have $\ntimes(h,k) = \next(\zero)$, and thus $h = k = \next(\zero)$, so that $a = b$ as claimed.
3. We have $h,k \in \nats$ such that $b = \ntimes(h,a)$ and $c = \ntimes(k,b)$. now $$c = \ntimes(\ntimes(h,k),a),$$ and thus $\ndiv(a,c)$.
</p></div>

<div class="test"><p>

> _test_div_reflexive :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_div_reflexive _ =
>   testName "div(a,a) == true" $
>   \a -> eq (div a a) True
> 
> 
> _test_div_antisymmetric :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_div_antisymmetric _ =
>   testName "if and(div(a,b),div(b,a)) then eq(a,b)" $
>   \a b -> if and (div a b) (div b a)
>     then eq a b
>     else True
> 
> 
> _test_div_transitive :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_div_transitive _ =
>   testName "if and(div(a,b),div(b,c)) then div(a,c)" $
>   \a b c -> if and (div a b) (div b c)
>     then div a c
>     else True

</p></div>
</div>

And $\ndiv$ interacts with the rest of arithmetic.

<div class="result">
<div class="thm">
Let $a,b,c,d \in \nats$. We have the following.

1. $\ndiv(a,\ntimes(b,a))$.
2. If $\ndiv(c,a)$, $c \neq \zero$, and $\ntimes(a,b) = \ntimes(c,d)$, then $\ndiv(b,d)$.
3. If $\ndiv(c,a)$ and $\ndiv(c,b)$ then $\ndiv(c,\nplus(a,b))$.
4. If $\ndiv(d,a)$ and $\ndiv(d,c)$ and $\nplus(a,b) = c$, then $\ndiv(d,b)$.
5. If $b \neq \zero$ and $\ndiv(a,b)$ then $\nleq(a,b)$.
</div>

<div class="proof"><p>
1. We have $\ntimes(b,a) = \ntimes(b,a)$.
2. Say $a = \ntimes(c,u)$. Now $$\ntimes(c,\ntimes(u,b)) = \ntimes(c,d),$$ so that $d = \ntimes(u,b)$. Thus $\ndiv(b,d)$ as claimed.
3. Say $a = \ntimes(h,c)$ and $b = \ntimes(k,c)$. Then by distributivity we have
$$\begin{eqnarray*}
 &   & \nplus(a,b) \\
 & = & \nplus(\ntimes(h,c),\ntimes(k,c)) \\
 & = & \ntimes(\nplus(h,k),c)
\end{eqnarray*}$$
as needed.
4. We consider two cases: either $d = \zero$ or $d = \next(m)$ for some $m$. If $d = \zero$, then we have $a = c = \zero$, and thus $b = \zero$. So $\ndiv(d,b)$ as claimed. Suppose now that $d = \next(m)$. Now $a = \ntimes(d,u)$ and $c = \ntimes(d,v)$ for some $u$ and $v$. Letting $(q,r) = \ndivalg(b,d)$, we have $$b = \nplus(\ntimes(q,d),r.$$ Now
$$\begin{eqnarray*}
 &   & \ntimes(d,v) \\
 & = & c \\
 & = & \nplus(a,b) \\
 & = & \nplus(\ntimes(d,u),\nplus(\ntimes(q,d),r)) \\
 & = & \nplus(\ntimes(d,\nplus(u,q)),r)
\end{eqnarray*}$$
so that $$r = \nminus(\ntimes(d,v),\ntimes(d,\nplus(u,q))) = \ntimes(d,\nminus(v,\nplus(u,q))).$$ Now $\nleq(r,m)$, so if $\nminus(v,\nplus(u,q)) \neq \zero$ we have $\nleq(\next(m),m)$, a contradiction. So we must have $\nminus(v,\nplus(u,q)) = \zero$, and thus $r = \zero$. So $\ndiv(d,b)$ as claimed.
5. Say $b = \ntimes(k,a)$; since $b \neq \zero$, we must also have $k \neq \zero$; say $k = \next(d)$. Then
$$\begin{eqnarray*}
 &   & b \\
 & = & \ntimes(k,a) \\
 & = & \ntimes(\next(k),a) \\
 & = & \nplus(\ntimes(k,a),a)
\end{eqnarray*}$$
so that $\nleq(a,b)$.
</p></div>

<div class="test"><p>

> _test_div_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_div_times _ =
>   testName "div(a,times(a,b))" $
>   \a b -> div a (times a b)
> 
> 
> _test_div_times_swap :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> n -> Bool)
> _test_div_times_swap _ =
>   testName "if div(c,a) and not(isZero(c)) and eq(times(a,b),times(c,d)) then div(b,d)" $
>   \a b c d -> if and (and (div c a) (not (isZero c))) (eq (times a b) (times c d))
>     then div b d
>     else True
> 
> 
> _test_div_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_div_plus _ =
>   testName "if and(div(c,a),div(c,b)) then div(c,plus(a,b))" $
>   \a b c -> if and (div c a) (div c b)
>     then div c (plus a b)
>     else True
> 
> 
> _test_div_plus_transfer :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> n -> Bool)
> _test_div_plus_transfer _ =
>   testName "if div(d,a) and div(d,c) and eq(plus(a,b),c) then div(d,b)" $
>   \a b c d -> if and (and (div d a) (div d c)) (eq c (plus a b))
>     then div d b
>     else True
> 
> 
> _test_div_leq :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_div_leq _ =
>   testName "if div(a,b) and not(isZero(b)) then leq(a,b)" $
>   \a b -> if and (div a b) (not (isZero b))
>     then leq a b
>     else True

</p></div>
</div>

$\ndiv$ interacts with $\nquo$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. If $\ndiv(b,a)$ and $c \neq \zero$, then $$\nquo(\ntimes(a,c),\ntimes(b,c)) = \nquo(a,b).$$
2. If $\ndiv(b,a)$, then $\nquo(\ntimes(c,a),b) = \ntimes(c,\nquo(a,b))$.
</div>

<div class="proof"><p>
1. We consider two cases: either $b = \zero$ or $b \neq \zero$. If $b = \zero$ then we have $a = \zero$, and
$$\begin{eqnarray*}
 &   & \nquo(a,b) \\
 & = & \nquo(\zero,\zero) \\
 & = & \nquo(\ntimes(\zero,c),\ntimes(\zero,c)) \\
 & = & \nquo(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed. Suppose instead that $b \neq \zero$; say $b = \next(m)$. Since $\ndiv(b,a)$, we have $a = \ntimes(d,b)$ for some $d$; since $\nleq(\zero,m)$, by the uniqueness of quotients by nonzero divisors we have $d = \nquo(a,b)$. But also $$\ntimes(a,c) = \ntimes(d,\ntimes(b,c)),$$ and since $\ntimes(b,c) \neq \zero$ we again have $$d = \nquo(\ntimes(a,c),\ntimes(b,c))$$ by the uniqueness of quotients by nonzero divisors. Thus $$\nquo(a,b) = \nquo(\ntimes(a,c),\ntimes(b,c))$$ as claimed.
2. We consider two cases: either $b = \zero$ or $b \neq \zero$. If $b = \zero$, we have $a = \zero$. Now
$$\begin{eqnarray*}
 &   & \nquo(\ntimes(c,a),b) \\
 & = & \nquo(\zero,\zero) \\
 & = & \zero \\
 & = & \ntimes(c,\zero) \\
 & = & \ntimes(c,\nquo(a,b))
\end{eqnarray*}$$
as claimed. Suppose then that $b \neq \zero$; say $b = \next(m)$. Now say $a = \ntimes(q,b)$, and by the uniqueness of quotients by a nonzero divisor, we have $q = \nquo(a,b)$. Now $\ntimes(c,a) = \ntimes(\ntimes(c,q),b)$, and again by the uniqueness of quotients by a nonzero divisor we have
$$\begin{eqnarray*}
 &   & \nquo(\ntimes(c,a),b) \\
 & = & \ntimes(c,q) \\
 & = & \ntimes(c,\nquo(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_div_quo_times_cancel :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_div_quo_times_cancel _ =
>   testName "if div(b,a) and not(isZero(c)) then quo(times(a,c),times(b,c)) == quo(a,b)" $
>   \a b c -> if and (div b a) (not (isZero c))
>     then eq (quo (times c a) (times c b)) (quo a b)
>     else True
> 
> 
> _test_div_quo_times_interchange :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_div_quo_times_interchange _ =
>   testName "if div(b,a) then quo(times(c,a),b) == times(c,quo(a,b))" $
>   \a b c -> if div b a
>     then eq (quo (times c a) b) (times c (quo a b))
>     else True

</p></div>
</div>

We'll call the next result the Cross Multiplication Theorem.

<div class="result">
<div class="thm">
Let $a,b,c,d \in \nats$ such that $\ndiv(b,a)$ and $\ndiv(d,c)$ and $b,d \neq \zero$. Then $$\ntimes(a,d) = \ntimes(b,c)$$ if and only if $\nquo(a,b) = \nquo(c,d).$$
</div>

<div class="proof"><p>
Since $b$ and $d$ are both not zero, using the uniqueness of quotients by nonzero divisors we have $$\ntimes(a,d) = \ntimes(b,c)$$ if and only if $$\nquo(\ntimes(a,d),b) = c$$ if and only if $$\ntimes(d,\nquo(a,b)) = c$$ if and only if $$\nquo(a,b) = \nquo(c,d)$$ as claimed.
</p></div>

<div class="test"><p>

> _test_div_cross_multiplication :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> n -> Bool)
> _test_div_cross_multiplication _ =
>   testName "if div(b,a) and div(d,c) and b /= 0 and d /= 0 then times(a,d) == times(b,c) iff quo(a,b) == quo(c,d)" $
>   \a b c d -> if and (and (div b a) (div d c)) (and (not (isZero b)) (not (isZero d)))
>     then eq (eq (times a d) (times b c)) (eq (quo a b) (quo c d))
>     else True

</p></div>
</div>


Testing
-------

Suite:

> _test_div ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_div n maxSize numCases = do
>   testLabel ("div: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_div_zero_right n)
>   runTest args (_test_div_zero_left n)
>   runTest args (_test_div_one_left n)
>   runTest args (_test_div_one_right n)
>   runTest args (_test_div_reflexive n)
>   runTest args (_test_div_antisymmetric n)
>   runTest args (_test_div_transitive n)
>   runTest args (_test_div_times n)
>   runTest args (_test_div_times_swap n)
>   runTest args (_test_div_plus n)
>   runTest args (_test_div_plus_transfer n)
>   runTest args (_test_div_leq n)
>   runTest args (_test_div_quo_times_cancel n)
>   runTest args (_test_div_quo_times_interchange n)
>   runTest args (_test_div_cross_multiplication n)

Main:

> main_div :: IO ()
> main_div = do
>   _test_div (zero :: Unary) 50 100
