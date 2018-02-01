---
title: Greatest Common Divisor
author: nbloomf
date: 2017-04-10
tags: arithmetic-made-difficult, literate-haskell
slug: gcd
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module GreatestCommonDivisor
>   ( gcd, _test_gcd, main_gcd
>   ) where
>
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Tuples
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> import NormRecursion

Today we'll define the greatest common divisor of two natural numbers. The usual way to do this (in books I've seen) is to define what it means to say that $d$ is a greatest common divisor of $a$ and $b$, then show (possibly nonconstructively) that any two $a$ and $b$ have a greatest common divisor, and finally establish the Euclidean algorithm that actually computes GCDs. We will work backwards: first *defining* the GCD of two natural numbers using the punchline of the Euclidean algorithm and then proving that the output of this function acts like the GCD.

Recall that the Euclidean algorithm says $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$ and $\ngcd(a,\zero) = a$. So it is recursive, but not in quite the way that (say) plus and times are recursive, because the recursion argument does not decrease by "one" at each step, but rather by some larger amount. This is exactly what norm recursion is for.

The signature of $\ngcd$ is $$\nats \times \nats \rightarrow \nats,$$ while norm recursion takes arguments with signature $$\varphi : A \rightarrow A, \eta : A \rightarrow \nats,\ \mathrm{and}\ \chi : A \rightarrow B,$$ and gives a function with signature $$A \rightarrow B.$$ So we have $A = \nats \times \nats$ and $B = \nats$, and thus we need $$\varphi : \nats \times \nats \rightarrow \nats \times \nats,$$ with $$\eta : \nats \times \nats \rightarrow \nats$$ an iterative norm against $\varphi$, and $$\chi : \nats \times \nats \rightarrow \nats.$$ Taking a cue from the Euclidean algorithm, if $$\ngcd(a,b) = \normrec{\varphi}{\eta}{\chi} = \bif{\iszero(\eta(a,b))}{\chi(a,b)}{\ngcd(\varphi(a,b))},$$ it seems reasonable to insist that $$\varphi(a,b) = (b,\nrem(a,b)).$$ But if $b = \zero$, the division algorithm gets weird -- to avoid this we'll instead make $$\varphi(a,b) = \bif{\iszero(b)}{(a,\zero)}{(b,\nrem(a,b))}.$$ The "stopping condition" on this recursion is that $b = \zero$, in which case we should output $\chi(a,b) = a$. What remains is to define $\eta$ so that $\eta(a,\zero) = \zero$, but also so that $\eta$ is a bona fide iterative norm. That is, we need

1. If $\eta(a,b) = \zero$, then $\eta(\varphi(a,b)) = \zero$.
2. If $\eta(a,b) = \next(m)$, then $\nleq(\eta(\varphi(a,b)),m)$.

To this end:

:::::: theorem :::::
Define $\varphi : \nats \times \nats \rightarrow \nats \times \nats$ by $$\varphi(a,b) = \bif{\iszero(b)}{(a,\zero)}{(b,\nrem(a,b))}.$$ Then $\eta : \nats \times \nats \rightarrow \nats$ given by $$\eta(a,b) = \bif{\iszero(b)}{\zero}{\bif{\nleq(a,b)}{\next(\nplus(a,b))}{\nplus(a,b)}}$$ is an iterative norm on $(A,(\zero,\zero),\varphi)$.

::: proof ::::::::::
Suppose $\eta(a,b) = \zero$. We have two possibilities; either $b = \zero$, or $\nplus(a,b) = \zero$, so that $a = b = \zero$. In either case we have $b = \zero$. So we have $\varphi(a,b) = (a,\zero)$, so that $\eta(\varphi(a,b)) = \zero$.

Suppose instead that $\eta(a,b) = \next(m)$. In particular $b \neq \zero$, so we have $\varphi(a,b) = (b,\nrem(a,b))$. Since $\nleq(\nrem(a,b),b)$ and $\nrem(a,b) \neq b$, we have
$$\begin{eqnarray*}
 &   & \eta(\varphi(a,b)) \\
 & = & \eta(b,\nrem(a,b)) \\
 & = & \bif{\iszero(\nrem(a,b))}{\zero}{\bif{\nleq(b,\nrem(a,b))}{\next(\nplus(b,\nrem(a,b)))}{\nplus(b,\nrem(a,b))}} \\
 & = & \bif{\iszero(\nrem(a,b))}{\zero}{\bif{\bfalse}{\next(\nplus(b,\nrem(a,b)))}{\nplus(b,\nrem(a,b))}} \\
 & = & \bif{\iszero(\nrem(a,b))}{\zero}{\nplus(b,\nrem(a,b))}; \\
\end{eqnarray*}$$
in particular, $$\nleq(\eta(\varphi(a,b)),\nplus(b,\nrem(a,b))).$$ Now if $\nleq(a,b) = \btrue$, we have $\eta(a,b) = \next(\nplus(a,b))$ and $\nleq(a,\nrem(a,b))$, so that $$\nleq(\nplus(b,\nrem(a,b)),\next(\nplus(a,b)))$$ as needed. If $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, so that $\nleq(\nrem(a,b),a)$ and $\nrem(a,b) \neq a$, and we have $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,b))$$ as needed.
::::::::::::::::::::

::: test :::::::::::

> phi :: (Natural n, Equal n) => Pair n n -> Pair n n
> phi (Pair a b) = if isZero b
>   then tup a zero
>   else tup b (rem a b)
> 
> 
> eta :: (Natural n) => Pair n n -> n
> eta (Pair a b) = if isZero b
>   then zero
>   else if leq a b
>     then next (plus a b)
>     else plus a b
> 
> 
> _test_gcd_eta_norm :: (Natural n, Equal n)
>   => n -> Test (Pair n n -> Bool)
> _test_gcd_eta_norm _ =
>   testName "eta is iterative norm" $
>   \x -> case unnext (eta x) of
>     Left () -> isZero (eta (phi x))
>     Right m -> leq (eta (phi x)) m

::::::::::::::::::::
::::::::::::::::::::

Now we can define $\ngcd$ in terms of norm recursion.

:::::: definition ::
Let $\varphi$ and $\eta$ be as defined in the previous theorem. We then define a map $\ngcd : \nats \times \nats \rightarrow \nats$ by $$\ngcd = \normrec{\varphi}{\eta}{\fst}.$$

In Haskell:

> gcd :: (Natural n, Equal n)
>   => n -> n -> n
> gcd a b = normRec phi eta fst (tup a b)

::::::::::::::::::::

Since $\ngcd$ is defined in terms of norm recursion, we can also characterize it as the unique solution to a functional equation. Note that here we use the fact that $$\bif{p}{a}{\bif{p}{b}{c}} = \bif{p}{a}{c}.$$

:::::: corollary :::
$\ngcd$ is the unique mapping $f : \nats \times \nats \rightarrow \nats$ such that for all $a,b \in \nats$, we have $$f(a,b) = \bif{\iszero(b)}{a}{f(b,\nrem(a,b))}.$$

::: test :::::::::::

> _test_gcd_equation :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_gcd_equation _ =
>   testName "gcd(a,b) = if iszero(b) then a else gcd(b,rem(a,b))" $
>   \a b -> eq
>     (gcd a b)
>     (if isZero b then a else gcd b (rem a b))

::::::::::::::::::::
::::::::::::::::::::

The next theorem characterizes $\ngcd(a,b)$ in terms of a useful "universal property": it is a common divisor of $a$ and $b$, and among the common divisors of $a$ and $b$, it is the "largest" in an appropriate sense.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have the following.

1. $\ndiv(\ngcd(a,b),a)$ and $\ndiv(\ngcd(a,b),b)$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$.

::: proof ::::::::::
1. We proceed by strong induction on $b$. For the base case $b = \zero$, note that $\ngcd(a,b) = a$, and we have $$\ndiv(\ngcd(a,b),a) = \ndiv(a,a) = \btrue$$ and $$\ndiv(\ngcd(a,b),b) = \ndiv(a,\zero) = \btrue$$ as needed. For the inductive step, suppose the conclusion holds for all $a$ and for all $b$ such that $\nleq(b,m)$, and let $b = \next(m)$ and $a \in \nats$. In this case we have $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$. By the induction hypothesis, we have $\ndiv(\ngcd(a,b),b)$ and $\ndiv(\ngcd(a,b),\nrem(a,b))$. Now $\ndiv(\ngcd(a,b),\ntimes(b,\nquo(a,b)))$, so we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \ndiv(\ngcd(a,b),\nplus(\ntimes(b,\nquo(a,b)),\nrem(a,b))) \\
 & = & \ndiv(\ngcd(a,b),a)
\end{eqnarray*}$$
as needed.
2. We again proceed by strong induction on $b$. For the base case $b = \zero$, suppose $\ndiv(c,a)$ and $\ndiv(c,b)$; now $\ngcd(a,b) = a$, so that $\ndiv(c,\ngcd(a,b))$ trivially. For the inductive step, suppose the implication holds for all $a$ and $c$ when $\nleq(b,m)$, and let $b = \next(m)$ with $a,c \in \nats$. Suppose further that $\ndiv(c,a)$ and $\ndiv(c,b)$. Now $\ndiv(c,\ntimes(b,\nquo(a,b)))$, so that $\ndiv(c,\nrem(a,b))$, and thus $\ndiv(c,\ngcd(a,b))$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_common_div :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_gcd_common_div _ =
>   testName "div(gcd(a,b),a) and div(gcd(a,b),b)" $
>   \a b -> and (div (gcd a b) a) (div (gcd a b) b)
> 
> 
> _test_gcd_greatest_common_div :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_greatest_common_div _ =
>   testName "if div(c,a) and div(c,b) then div(c,gcd(a,b))" $
>   \a b c -> if and (div c a) (div c b)
>     then div c (gcd a b)
>     else true

::::::::::::::::::::
::::::::::::::::::::

And $\ngcd(a,b)$ is unique with this property.

:::::: theorem :::::
Let $a,b,c \in \nats$. Suppose $m \in \nats$ satisfies the following.

1. $\ndiv(m,a)$ and $\ndiv(m,b)$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,m)$.

Then $m = \ngcd(a,b)$.

::: proof ::::::::::
Since $\ndiv(m,a)$ and $\ndiv(m,b)$, we have $\ndiv(m,\ngcd(a,b))$. But a similar argument shows that $\ndiv(\ngcd(a,b),m)$. By antisymmetry we have $m = \ngcd(a,b)$ as claimed.
::::::::::::::::::::
::::::::::::::::::::

Then $\ngcd$ is commutative.

:::::: theorem :::::
Let $a,b \in \nats$. Then $\ngcd(a,b) = \ngcd(b,a)$.

::: proof ::::::::::
Note that $\ngcd(b,a)$ divides $a$ and $\ngcd(b,a)$ divides $b$, and if $c$ is a common divisor of $a$ and $b$ then $c$ divides $\ngcd(b,a)$. By the uniqueness of GCD we have $\ngcd(b,a) = \ngcd(a,b)$.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_commutative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_gcd_commutative _ =
>   testName "gcd(a,b) == gcd(b,a)" $
>   \a b -> eq (gcd a b) (gcd b a)

::::::::::::::::::::
::::::::::::::::::::

And $\ngcd$ is idempotent:

:::::: theorem :::::
Let $a \in \nats$. Then $$\ngcd(a,a) = a.$$

::: proof ::::::::::
$a$ divides $a$ and $a$ divides $a$, and if $c$ divides both $a$ and $a$ then $c$ divides $a$.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_idempotent :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_gcd_idempotent _ =
>   testName "gcd(a,a) == a" $
>   \a -> eq (gcd a a) a

::::::::::::::::::::
::::::::::::::::::::

And some special cases.

:::::: theorem :::::
For all $a \in \nats$ we have the following.

1. $\ngcd(a,\zero) = a$.
2. $\ngcd(a,\next(\zero)) = \next(\zero)$.
3. If $\ngcd(a,b) = \zero$, then $a = b = \zero$.

::: proof ::::::::::
1. Note that $a$ divides $a$ and $a$ divides $\zero$, and if $c$ divides both $a$ and $\zero$ then $c$ divides $a$.
2. Note that $\next(\zero)$ divides $a$ and $\next(\zero)$ divides $\next(\zero)$, and if $c$ divides $\next(\zero)$ then $c = \next(\zero)$.
3. We proceed by strong induction on $b$. For the base case $b = \zero$, note that $$a = \ngcd(a,\zero) = \zero$$ as claimed. Now suppose we have $n$ such that the implication holds for all $b$ with $\nleq(b,n)$, and that $b = \next(n)$. Now $$\zero = \ngcd(a,b) = \ngcd(b,\nrem(a,b)),$$ where $\nleq(\nrem(a,b),b)$. By the induction hypothesis we have $b = \zero$ and $\nrem(a,b) = \zero$, so that $$a = \nplus(\ntimes(\nquo(a,b),b),\nrem(a,b)) = \zero$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_gcd_zero _ =
>   testName "gcd(a,0) == a" $
>   \a -> eq a (gcd a zero)
> 
> 
> _test_gcd_one :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_gcd_one _ =
>   testName "gcd(a,next(0)) == next(0)" $
>   \a -> eq (next zero) (gcd a (next zero))
> 
> 
> _test_gcd_zero_args :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_gcd_zero_args _ =
>   testName "if iszero(gcd(a,b)) then and(iszero(a),iszero(b))" $
>   \a b -> if isZero (gcd a b)
>     then and (isZero a) (isZero b)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\ngcd$ is associative.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then we have $\ngcd(\ngcd(a,b),c) = \ngcd(a,\ngcd(b,c))$.

::: proof ::::::::::
Let $h = \ngcd(\ngcd(a,b),c)$, $k = \ngcd(a,\ngcd(b,c))$, $u = \ngcd(a,b)$, and $v = \ngcd(b,c)$. First we show that $\ndiv(h,k)$. Note that $\ndiv(h,u)$, so that $\ndiv(h,a)$ and $\ndiv(h,b)$. Now $\ndiv(h,c)$, so that $\ndiv(h,v)$. Thus $\ndiv(h,k)$. The proof that $\ndiv(k,h)$ is similar; thus $h = k$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_associative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_associative _ =
>   testName "gcd(gcd(a,b),c) == gcd(a,gcd(b,c))" $
>   \a b c -> eq (gcd (gcd a b) c) (gcd a (gcd b c))

::::::::::::::::::::
::::::::::::::::::::

$\ngcd$ detects $\ndiv$.

:::::: theorem :::::
Let $a,b \in \nats$. Then $\ngcd(a,b) = a$ if and only if $\ndiv(a,b)$.

::: proof ::::::::::
Certainly if $\ngcd(a,b) = a$, then $\ndiv(a,b)$. Suppose conversely that $\ndiv(a,b)$. We consider two cases: either $a = \zero$ or $a = \next(t)$ for some $t$. If $a = \zero$, then $b = \zero$, and we have $$\ngcd(a,b) = \zero = a$$ as claimed. Suppose now that $a = \next(t)$. Since $\ndiv(a,b)$, we have $$b = \ntimes(q,a) = \nplus(\ntimes(q,a),\zero)$$ for some $q$. Now $\nleq(\zero,t)$, and by the uniqueness of remainders by nonzero divisors, we have $\nrem(b,a) = \zero$. So we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \ngcd(b,a) \\
 & = & \ngcd(a,\nrem(b,a)) \\
 & = & \ngcd(a,\zero) \\
 & = & a
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_div :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_gcd_div _ =
>   testName "eq(gcd(a,b),a) == div(a,b)" $
>   \a b -> eq (eq (gcd a b) a) (div a b)

::::::::::::::::::::
::::::::::::::::::::

$\ngcd$ distributes over $\ntimes$.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then $\ngcd(\ntimes(a,c),\ntimes(b,c)) = \ntimes(\ngcd(a,b),c)$.

::: proof ::::::::::
We consider two cases: either $c = \zero$ or $c \neq \zero$. If $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \ntimes(\ngcd(a,b),c) \\
 & = & \zero \\
 & = & \ngcd(\zero,\zero) \\
 & = & \ngcd(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed. Now suppose $c \neq \zero$. First note that $\ndiv(\ngcd(a,b),a)$, so that $$\ndiv(\ntimes(\ngcd(a,b),c),\ntimes(a,c)).$$ Similarly, we have $$\ndiv(\ntimes(\ngcd(a,b),c),\ntimes(b,c)).$$ Thus $$\ndiv(\ntimes(\ngcd(a,b),c), \ngcd(\ntimes(a,c),\ntimes(b,c))).$$ Now note that $\ndiv(c,\ntimes(a,c))$ and $\ndiv(c,\ntimes(b,c))$, so that $$\ndiv(c,\ngcd(\ntimes(a,c),\ntimes(b,c))).$$ Say $$\ntimes(u,c) = \ngcd(\ntimes(a,c),\ntimes(b,c)).$$ Now $\ndiv(\ntimes(u,c),\ntimes(a,c))$, so that $\ndiv(u,a)$; similarly, $\ndiv(u,b)$. Thus $\ndiv(u,\ngcd(a,b))$, and we have $$\ndiv(\ngcd(\ntimes(a,c),\ntimes(b,c)),\ntimes(\ngcd(a,b),c)).$$ By the antisymmetry of $\ndiv$, we have $$\ngcd(\ntimes(a,c),\ntimes(b,c)) = \ntimes(\ngcd(a,b),c)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_distributive_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_distributive_times _ =
>   testName "times(gcd(a,b),c) == gcd(times(a,c),times(b,c))" $
>   \a b c -> eq (times (gcd a b) c) (gcd (times a c) (times b c))

::::::::::::::::::::
::::::::::::::::::::

$\ngcd$ is compatible with $\ndiv$.

:::::: theorem :::::
Let $a,b,c \in \nats$. If $\ndiv(a,b)$, then $\ndiv(\ngcd(a,c),\ngcd(b,c))$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \ngcd(\ngcd(a,c),\ngcd(b,c)) \\
 & = & \ngcd(\ngcd(a,b),\ngcd(c,c)) \\
 & = & \ngcd(a,c).
\end{eqnarray*}$$
Thus $\ndiv(\ngcd(a,c),\ngcd(b,c))$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_div_compatible :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_div_compatible _ =
>   testName "if div(a,b) then div(gcd(a,c),gcd(b,c))" $
>   \a b c -> if div a b
>     then div (gcd a c) (gcd b c)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\nquo$ kind of distributes over $\ngcd$.

:::::: theorem :::::
Let $a,b,c \in \nats$. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $$\ngcd(\nquo(a,c),\nquo(b,c)) = \nquo(\ngcd(a,b),c).$$

::: proof ::::::::::
We consider two cases: either $c = \zero$ or $c \neq \zero$. If $c = \zero$, then $\nquo(a,c) = \zero$ and $\nquo(b,c) = \zero$, so we have
$$\begin{eqnarray*}
 &   & \ngcd(\nquo(a,c),\nquo(b,c)) \\
 & = & \ngcd(\zero,\zero) \\
 & = & \zero \\
 & = & \nquo(\ngcd(a,b),c)
\end{eqnarray*}$$
as claimed. Suppose now that $c \neq \zero$. Say $a = \ntimes(c,u)$ and $b = \ntimes(c,v)$. Note that
$$\begin{eqnarray*}
 &   & \ntimes(c,\ngcd(u,v)) \\
 & = & \ngcd(\ntimes(c,u),\ntimes(c,v)) \\
 & = & \ngcd(a,b).
\end{eqnarray*}$$
By the uniqueness of quotients by nonzero divisors, $$\nquo(\ngcd(a,b),c) = \ngcd(\nquo(a,c),\nquo(b,c))$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_gcd_div_quo :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_gcd_div_quo _ =
>   testName "if div(c,a) and div(c,b) then gcd(quo(a,c),quo(b,c)) == quo(gcd(a,b),c)" $
>   \a b c -> if and (div c a) (div c b)
>     then eq (gcd (quo a c) (quo b c)) (quo (gcd a b) c)
>     else true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_gcd ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_gcd n maxSize numCases = do
>   testLabel1 "gcd" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_gcd_eta_norm n)
>   runTest args (_test_gcd_equation n)
>   runTest args (_test_gcd_common_div n)
>   runTest args (_test_gcd_greatest_common_div n)
>   runTest args (_test_gcd_commutative n)
>   runTest args (_test_gcd_idempotent n)
>   runTest args (_test_gcd_zero n)
>   runTest args (_test_gcd_one n)
>   runTest args (_test_gcd_zero_args n)
>   runTest args (_test_gcd_associative n)
>   runTest args (_test_gcd_div n)
>   runTest args (_test_gcd_distributive_times n)
>   runTest args (_test_gcd_div_compatible n)
>   runTest args (_test_gcd_div_quo n)

Main:

> main_gcd :: IO ()
> main_gcd = do
>   _test_gcd (zero :: Unary) 20 100
