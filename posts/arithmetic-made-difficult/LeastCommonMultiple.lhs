---
title: Least Common Multiple
author: nbloomf
date: 2017-04-12
tags: arithmetic-made-difficult, literate-haskell
slug: lcm
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module LeastCommonMultiple
>   ( lcm, _test_lcm, main_lcm
>   ) where
>
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> import GreatestCommonDivisor
> import CoprimeTo

Recall the following property of $\nmax$: if $\nleq(c,a)$ and $\nleq(c,b)$, then $\nleq(c,\nmax(a,b))$. This statement fell out of the definition of $\nmax$ without much fuss, and may seem anticlimactic. But compare it to this analogous statement about $\ngcd$: if $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$. Now $\nmax$ and $\ngcd$ seem to play very similar roles. Where $\nleq$ is a kind of "additive order" on $\nats$ and $\nmax$ gives an additive ceiling to $a$ and $b$, $\ndiv$ is a kind of "multiplicative order" and $\ngcd$ gives a multiplicative ceiling to $a$ and $b$. When an analogy this strong holds between two concepts in mathematics, it is frequently useful to see how far the analogy goes. To that end, today we will define the multiplicative counterpart to $\nmin$.

We don't need recursion for this.

:::::: definition ::
Define $\nlcm : \nats \times \nats \rightarrow \nats$ by $$\nlcm(a,b) = \nquo(\ntimes(a,b),\ngcd(a,b)).$$

In Haskell:

> lcm :: (Natural n, Equal n) => n -> n -> n
> lcm a b = quo (times a b) (gcd a b)

::::::::::::::::::::

woo special cases!

:::::: theorem :::::
For all $a \in \nats$ we have the following.

1. $\nlcm(a,\zero) = \zero$.
2. $\nlcm(a,\next(\zero)) = a$.

::: proof ::::::::::
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
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_lcm_zero _ =
>   testName "lcm(a,0) == 0" $
>   \a -> eq zero (lcm a zero)
> 
> 
> _test_lcm_one :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_lcm_one _ =
>   testName "lcm(a,next(0)) == a" $
>   \a -> eq a (lcm a (next zero))

::::::::::::::::::::
::::::::::::::::::::

As we might expect, $\nlcm$ enjoys many properties analogous to those of $\ngcd$. It is idempotent and commutative.

:::::: theorem :::::
Let $a,b \in \nats$. Then we have the following.

1. $\nlcm(a,a) = a$.
2. $\nlcm(a,b) = \nlcm(b,a)$.

::: proof ::::::::::
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
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_idempotent :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_lcm_idempotent _ =
>   testName "lcm(a,a) == a" $
>   \a -> eq (lcm a a) a
> 
> 
> _test_lcm_commutative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_lcm_commutative _ =
>   testName "lcm(a,b) == lcm(b,a)" $
>   \a b -> eq (lcm a b) (lcm b a)

::::::::::::::::::::
::::::::::::::::::::

And the universal property:

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have the following.

1. $\ndiv(a,\nlcm(a,b))$ and $\ndiv(b,\nlcm(a,b))$.
2. If $\ndiv(a,c)$ and $\ndiv(b,c)$, then $\ndiv(\nlcm(a,b),c)$.

::: proof ::::::::::
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
2. Suppose we have $\ndiv(a,c)$ and $\ndiv(b,c)$. We consider two cases: either $(a,b) = (\zero,\zero)$ or $(a,b) \neq (\zero,\zero)$. First suppose $(a,b) = (\zero,\zero)$. Now $c = \zero$, and we have $\ndiv(\nlcm(a,b),\zero)$ as claimed. Suppose instead that $(a,b) \neq (\zero,\zero)$. Say $c = \ntimes(a,u)$ and $c = \ntimes(b,v)$. Now let $d = \ngcd(a,b)$ (note that $d \neq \zero$) and say $a = \ntimes(d,s)$ and $b = \ntimes(d,t)$. Note that $\ncoprime(s,t)$. Now we have
$$\begin{eqnarray*}
c & = & c \\
\ntimes(a,u) & = & \ntimes(b,v) \\
\ntimes(\ntimes(d,s),u) & = & \ntimes(\ntimes(d,t),v) \\
\ntimes(d,\ntimes(s,u)) & = & \ntimes(d,\ntimes(d,t)) \\
\ntimes(s,u) & = & \ntimes(t,v).
\end{eqnarray*}$$
That is, $\ndiv(t,\ntimes(s,u))$. By Euclid's lemma, we have $\ndiv(t,u)$. Next, note that
$$\begin{eqnarray*}
 &   & \nlcm(a,b) \\
 & = & \nquo(\ntimes(a,b),\ngcd(a,b)) \\
 & = & \nquo(\ntimes(a,\ntimes(t,d)),d) \\
 &     \href{@times@#thm-times-associative}
   = & \nquo(\ntimes(\ntimes(a,t),d),d) \\
 & = & \ntimes(a,t).
\end{eqnarray*}$$
Since $c = \ntimes(a,u)$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \ndiv(t,u) \\
 & = & \ndiv(\ntimes(a,t),\ntimes(a,u)) \\
 & = & \ndiv(\nlcm(a,b),c)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_div_args :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_lcm_div_args _ =
>   testName "div(a,lcm(a,b)) and div(b,lcm(a,b))" $
>   \a b -> and (div a (lcm a b)) (div b (lcm a b))
> 
> 
> _test_lcm_least_common :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_lcm_least_common _ =
>   testName "if div(a,c) and div(b,c) then div(lcm(a,b),c)" $
>   \a b c -> if and (div a c) (div b c)
>     then div (lcm a b) c
>     else true

::::::::::::::::::::
::::::::::::::::::::

And $\nlcm(a,b)$ is unique with this property.

:::::: theorem :::::
Let $a,b,c \in \nats$. Suppose $m \in \nats$ satisfies the following.

1. $\ndiv(a,m)$ and $\ndiv(b,m)$.
2. If $\ndiv(a,c)$ and $\ndiv(b,c)$, then $\ndiv(m,c)$.

Then $m = \nlcm(a,b)$.

::: proof ::::::::::
Since $\ndiv(a,m)$ and $\ndiv(b,m)$, we have $\ndiv(\nlcm(a,b),m)$. But likewise we have $\ndiv(m,\nlcm(a,b))$. By antisymmetry, we have $m = \nlcm(a,b)$ as claimed.
::::::::::::::::::::
::::::::::::::::::::

$\nlcm$ is associative:

:::::: theorem :::::
Let $a,b,c \in \nats$. Then $\nlcm(\nlcm(a,b),c) = \nlcm(a,\nlcm(b,c))$.

::: proof ::::::::::
Note that $\ndiv(a,\nlcm(a,\nlcm(b,c)))$. We also have $\ndiv(b,\nlcm(b,c))$, so that $$\ndiv(b,\nlcm(a,\nlcm(b,c)))$$ by transitivity; similarly, $$\ndiv(c,\nlcm(a,\nlcm(b,c))).$$ By the universal property of $\nlcm$, we thus have $$\ndiv(\nlcm(a,b),\nlcm(a,\nlcm(b,c))),$$ so that $$\ndiv(\nlcm(\nlcm(a,b),c),\nlcm(a,\nlcm(b,c))).$$ A similar argument shows that $$\ndiv(\nlcm(a,\nlcm(b,c)),\nlcm(\nlcm(a,b),c)).$$ By antisymmetry, we thus have $$\nlcm(a,\nlcm(b,c)) = \nlcm(\nlcm(a,b),c)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_associative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_lcm_associative _ =
>   testName "lcm(lcm(a,b),c) == lcm(a,lcm(b,c))" $
>   \a b c -> eq (lcm (lcm a b) c) (lcm a (lcm b c))

::::::::::::::::::::
::::::::::::::::::::

$\nlcm$ detects $\ndiv$.

:::::: theorem :::::
Let $a,b \in \nats$. Then $\nlcm(a,b) = a$ if and only if $\ndiv(b,a)$.

::: proof ::::::::::
First suppose $\ndiv(b,a)$; say $a = \ntimes(b,d)$. Now $\ndiv(a,a)$ and $\ndiv(b,a)$, and if $\ndiv(c,a)$ and $\ndiv(c,b)$ then $\ndiv(c,a)$. By the universal property of $\nlcm$ we have $a = \nlcm(a,b)$. Conversely, suppose $a = \nlcm(a,b)$. We consider two cases: either $(a,b) = (\zero,\zero)$ or $(a,b) \neq (\zero,\zero)$. If $(a,b) = (\zero,\zero)$ then $\ndiv(b,a)$ as needed. Suppose then that $(a,b) \neq (\zero,\zero)$. If $a = \zero$, then $\ndiv(b,a)$ as claimed. Suppose $a \neq \zero$. Now let $d = \ngcd(a,b)$; note that $d \neq \zero$. Say $b = \ntimes(k,d)$. Now
$$\begin{eqnarray*}
 &   & \ntimes(a,\next(\zero)) \\
 &     \href{@times@#thm-times-one-right}
   = & a \\
 & = & \nlcm(a,b) \\
 & = & \nquo(\ntimes(a,b),\ngcd(a,b)) \\
 & = & \nquo(\ntimes(\ntimes(a,k),d),d) \\
 & = & \ntimes(a,k).
\end{eqnarray*}$$
Since $a \neq \zero$, we have $k = \next(\zero)$, and thus $b = \ngcd(a,b)$. Hence $\ndiv(b,a)$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_div :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_lcm_div _ =
>   testName "lcm(a,b) == a if and only if ndiv(b,a)" $
>   \a b -> eq (eq a (lcm a b)) (div b a)

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ distributes over $\nlcm$.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have $$\nlcm(\ntimes(c,a),ntimes(c,b)) = \ntimes(c,\nlcm(a,b)).$$

::: proof ::::::::::
We consider two cases: either $c = \zero$ or $c \neq \zero$. If $c = \zero$ we have
$$\begin{eqnarray*}
 &   & \nlcm(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \nlcm(\zero,\zero) \\
 & = & \zero \\
 &     \href{@times@#cor-times-up-zero}
   = & \ntimes(\zero,\nlcm(a,b)) \\
 & = & \ntimes(c,\nlcm(a,b))
\end{eqnarray*}$$
as claimed. Suppose then that $c \neq \zero$. Now we have
$$\begin{eqnarray*}
 &   & \nlcm(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \nquo(\ntimes(\ntimes(c,a),\ntimes(c,b)),\ngcd(\ntimes(c,a),\ntimes(c,b))) \\
 & = & \nquo(\ntimes(\ntimes(c,\ntimes(a,b)),c),\ngcd(\ntimes(a,b),c)) \\
 & = & \nquo(\ntimes(c,\ntimes(a,b)),\ngcd(a,b)) \\
 & = & \ntimes(c,\nquo(\ntimes(a,b),\ngcd(a,b))) \\
 & = & \ntimes(c,\nlcm(a,b))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_distributive_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_lcm_distributive_times _ =
>   testName "lcm(times(c,a),times(c,b)) == times(c,lcm(a,b))" $
>   \a b c -> eq (lcm (times c a) (times c b)) (times c (lcm a b))

::::::::::::::::::::
::::::::::::::::::::

$\nlcm$ is compatible with $\ndiv$.

:::::: theorem :::::
Let $a,b,c \in \nats$. If $\ndiv(a,b)$, then $\ndiv(\nlcm(a,c),\nlcm(b,c))$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \nlcm(\nlcm(a,c),\nlcm(b,c)) \\
 & = & \nlcm(\nlcm(a,b),\nlcm(c,c)) \\
 & = & \nlcm(b,c)
\end{eqnarray*}$$
so that $\ndiv(\nlcm(a,c),\nlcm(b,c))$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_div_compatible :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_lcm_div_compatible _ =
>   testName "if div(a,b) then div(lcm(a,c),lcm(b,c))" $
>   \a b c -> if div a b
>     then div (lcm a c) (lcm b c)
>     else true

::::::::::::::::::::
::::::::::::::::::::

Finally, $\ngcd$ and $\nlcm$ distribute over each other.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have the following.

1. $\ngcd(a,\nlcm(b,c)) = \nlcm(\ngcd(a,b),\ngcd(a,c))$.
2. $\nlcm(a,\ngcd(b,c)) = \ngcd(\nlcm(a,b),\nlcm(a,c))$.

::: proof ::::::::::
The proofs of these two results will not be painful, but they are a little tedious, especially with the notation we're using for arithmetic. So for this proof -- and this proof only! -- I'll make two concessions to readability. Because $\ngcd$ is associative, there is no ambiguity in an expression like $$\ngcd(a,b,c).$$ Also, we will denote $\ntimes(a,b)$ by juxtaposition (like we're used to anyway, but have been avoiding).

1. First suppose $a = \zero$; note that
$$\begin{eqnarray*}
 &   & \ngcd(a,\nlcm(b,c)) \\
 & = & \ngcd(\zero,\nlcm(b,c)) \\
 & = & \nlcm(b,c) \\
 & = & \nlcm(\ngcd(\zero,b),\ngcd(\zero,c)) \\
 & = & \nlcm(\ngcd(a,b),\ngcd(a,c))
\end{eqnarray*}$$
as claimed. Next suppose $b = \zero$. Now we have
$$\begin{eqnarray*}
 &   & \ngcd(a,\nlcm(b,c)) \\
 & = & \ngcd(a,\nlcm(\zero,c)) \\
 & = & \ngcd(a,\zero) \\
 & = & a \\
 & = & \nlcm(\ngcd(a,b),a) \\
 & = & \nlcm(\ngcd(a,b),\ngcd(a,\zero)) \\
 & = & \nlcm(\ngcd(a,b),\ngcd(a,c))
\end{eqnarray*}$$
as claimed. Similarly, if $c = \zero$ we have
$$\begin{eqnarray*}
 &   & \ngcd(a,\nlcm(b,c)) \\
 & = & \ngcd(a,\nlcm(b,\zero)) \\
 & = & \ngcd(a,\zero) \\
 & = & a \\
 & = & \nlcm(a,\ngcd(a,c)) \\
 & = & \nlcm(\ngcd(a,\zero),\ngcd(b,c)) \\
 & = & \nlcm(\ngcd(a,c),\ngcd(b,c))
\end{eqnarray*}$$
as claimed. We can now assume that $a$, $b$, and $c$ are not zero; in particular, $\ngcd(b,c)$ and $\ngcd(a,\ngcd(b,c))$ are not zero. We begin with a sub-result. Note that
$$\begin{eqnarray*}
 &   & \ngcd(a\ngcd(b,c),bc)\ngcd(a,\ngcd(b,c)) \\
 & = & \ngcd(\ngcd(ab,ac),bc)\ngcd(a,b,c) \\
 & = & \ngcd(ab,ac,bc)\ngcd(a,b,c) \\
 & = & \ngcd(ab\ngcd(a,b,c),ac\ngcd(a,b,c),bc\ngcd(a,b,c)) \\
 & = & \ngcd(aba,abb,abc,aca,acb,acc,bca,bcb,bcc) \\
 & = & \ngcd(aab,aac,acb,acc,bab,bac,bcb,bcc) \\
 & = & \ngcd(aa\ngcd(b,c),ac\ngcd(b,c),ba\ngcd(b,c),bc\ngcd(b,c)) \\
 & = & \ngcd(aa,ac,ba,bc)\ngcd(b,c) \\
 & = & \ngcd(a\ngcd(a,c),b\ngcd(a,c))\ngcd(b,c) \\
 & = & \ngcd(a,b)\ngcd(a,c)\ngcd(b,c).
\end{eqnarray*}$$
Note that $$\ndiv(\ngcd(b,c),a\ngcd(b,c))$$ and $$\ndiv(\ngcd(b,c),bc),$$ so that $$\ndiv(\ngcd(b,c),\ngcd(a\ngcd(b,c),bc));$$ thus we also have $$\ndiv(\ngcd(a,\ngcd(b,c)),\ngcd(a,b)\ngcd(a,c)).$$
By cross-multiplication, we have
$$\begin{eqnarray*}
 &   & \nquo(\ngcd(a\ngcd(b,c),bc),\ngcd(b,c)) \\
 & = & \nquo(\ngcd(a,b)\ngcd(a,c),\ngcd(a,\ngcd(b,c))).
\end{eqnarray*}$$
Thus we have
$$\begin{eqnarray*}
 &   & \ngcd(a,\nlcm(b,c)) \\
 & = & \ngcd(a,\nquo(bc,\ngcd(b,c))) \\
 & = & \ngcd(\nquo(a\ngcd(b,c),\ngcd(b,c)),\nquo(bc,\ngcd(b,c))) \\
 & = & \nquo(\ngcd(a\ngcd(b,c),bc),\ngcd(b,c)) \\
 & = & \nquo(\ngcd(a,b)\ngcd(a,c),\ngcd(a,\ngcd(b,c))) \\
 & = & \nquo(\ngcd(a,b)\ngcd(a,c),\ngcd(\ngcd(a,b),\ngcd(a,c))) \\
 & = & \nlcm(\ngcd(a,b),\ngcd(a,c))
\end{eqnarray*}$$
as claimed.
2. First suppose $a = \zero$. Then we have
$$\begin{eqnarray*}
 &   & \nlcm(a,\ngcd(b,c)) \\
 & = & \nlcm(\zero,\ngcd(b,c)) \\
 & = & \zero \\
 & = & \ngcd(\zero,\zero) \\
 & = & \ngcd(\nlcm(\zero,b),\nlcm(\zero,c)) \\
 & = & \ngcd(\nlcm(a,b),\nlcm(a,c))
\end{eqnarray*}$$
as claimed. Next suppose $b = \zero$. Then we have
$$\begin{eqnarray*}
 &   & \nlcm(a,\ngcd(b,c)) \\
 & = & \nlcm(a,\ngcd(\zero,c)) \\
 & = & \nlcm(a,c) \\
 & = & \ngcd(\zero,\nlcm(a,c)) \\
 & = & \ngcd(\nlcm(a,\zero),\nlcm(a,c)) \\
 & = & \ngcd(\nlcm(a,b),\nlcm(a,c))
\end{eqnarray*}$$
as claimed. Similarly, if $c = \zero$ we have
$$\begin{eqnarray*}
 &   & \nlcm(a,\ngcd(b,c)) \\
 & = & \nlcm(a,\ngcd(b,\zero)) \\
 & = & \nlcm(a,b) \\
 & = & \ngcd(\nlcm(a,b),\zero) \\
 & = & \ngcd(\nlcm(a,b),\nlcm(a,\zero)) \\
 & = & \ngcd(\nlcm(a,b),\nlcm(a,c))
\end{eqnarray*}$$
as claimed. We can now assume that $a$, $b$, and $c$ are not zero; in particular, $\ngcd(a,b)\ngcd(a,c)$ and $\ngcd(a,\ngcd(b,c))$ are not zero; in particular, $\ngcd(a,b)\ngcd(a,c)$ and $\ngcd(a,\ngcd(b,c))$ are not zero. We begin with a sub-result. Note that
$$\begin{eqnarray*}
 &   & a\ngcd(a,\ngcd(b,c))\ngcd(ba,bc,ca,cb) \\
 & = & a\ngcd(a,b,c)\ngcd(ba,bc,ca,cb) \\
 & = & a\ngcd(a\ngcd(ba,bc,ca,cb),b\ngcd(ba,bc,ca,cb),c\ngcd(ba,bc,ca,cb)) \\
 & = & a\ngcd(\ngcd(aba,abc,aca,acb),\ngcd(bba,bbc,bca,bcb),\ngcd(cba,cbc,cca,ccb)) \\
 & = & a\ngcd(aba,abc,aca,acb,bba,bbc,bca,bcb,cba,cbc,cca,ccb) \\
 & = & a\ngcd(aab,aac,acb,acc,bab,bac,bcb,bcc) \\
 & = & a\ngcd(aa\ngcd(b,c),ac\ngcd(b,c),ba\ngcd(b,c),bc\ngcd(b,c)) \\
 & = & a\ngcd(aa,ac,ba,bc)\ngcd(b,c) \\
 & = & a\ngcd(a\ngcd(a,c),b\ngcd(a,c))\ngcd(b,c) \\
 & = & a\ngcd(a,b)\ngcd(a,c)\ngcd(b,c).
\end{eqnarray*}$$
Note that $$\ndiv(\ngcd(a,\ngcd(b,c)),a\ngcd(b,c)),$$ so that $$\ndiv(\ngcd(a,b)\ngcd(a,c),a\ngcd(ba,bc,ca,cb)).$$ By cross-multiplication, we have
$$\begin{eqnarray*}
 &   & \nquo(a\ngcd(ba,bc,ca,cb),\ngcd(a,b)\ngcd(a,c)) \\
 & = & \nquo(a\ngcd(b,c),\ngcd(a,\ngcd(b,c))).
\end{eqnarray*}$$
Thus we have
$$\begin{eqnarray*}
 &   & \ngcd(\nlcm(a,b),\nlcm(a,c)) \\
 & = & \ngcd(\nquo(ab,\ngcd(a,b)),\nquo(ac,\ngcd(a,c))) \\
 & = & \ngcd(\nquo(ab\ngcd(a,c),\ngcd(a,b)\ngcd(a,c)),\nquo(ac\ngcd(a,b),\ngcd(a,b)\ngcd(a,c))) \\
 & = & \nquo(\ngcd(ab\ngcd(a,c),ac\ngcd(a,b)),\ngcd(a,b)\ngcd(a,c)) \\
 & = & \nquo(a\ngcd(b\ngcd(a,c),c\ngcd(a,b)),\ngcd(a,b)\ngcd(a,c)) \\
 & = & \nquo(a\ngcd(ba,bc,ca,cb),\ngcd(a,b)\ngcd(a,c)) \\
 & = & \nquo(a\ngcd(b,c),\ngcd(a,\ngcd(b,c))) \\
 & = & \nlcm(a,\ngcd(b,c))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcm_distributive_gcd :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_lcm_distributive_gcd _ =
>   testName "lcm(gcd(c,a),gcd(c,b)) == gcd(c,lcm(a,b))" $
>   \a b c -> eq (lcm (gcd c a) (gcd c b)) (gcd c (lcm a b))
> 
> 
> _test_gcd_distributive_lcm :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_distributive_lcm _ =
>   testName "gcd(lcm(c,a),lcm(c,b)) == lcm(c,gcd(a,b))" $
>   \a b c -> eq (gcd (lcm c a) (lcm c b)) (lcm c (gcd a b))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_lcm ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_lcm n maxSize numCases = do
>   testLabel1 "lcm" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_lcm_zero n)
>   runTest args (_test_lcm_one n)
>   runTest args (_test_lcm_idempotent n)
>   runTest args (_test_lcm_commutative n)
>   runTest args (_test_lcm_div_args n)
>   runTest args (_test_lcm_least_common n)
>   runTest args (_test_lcm_associative n)
>   runTest args (_test_lcm_div n)
>   runTest args (_test_lcm_distributive_times n)
>   runTest args (_test_lcm_div_compatible n)
>   runTest args (_test_lcm_distributive_gcd n)
>   runTest args (_test_gcd_distributive_lcm n)

Main:

> main_lcm :: IO ()
> main_lcm = do
>   _test_lcm (zero :: Unary) 20 100
