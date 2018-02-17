---
title: Subtraction
author: nbloomf
date: 2017-04-02
tags: arithmetic-made-difficult, literate-haskell
slug: minus
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Minus
>   ( minus, _test_minus, main_minus
>   ) where
>
> import Testing
> import Booleans
> import And
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import Times

We'd eventually like to solve some equations; for instance, one of the simplest equations we can construct with the tools we have so far is $$\nplus(a,x) = b$$ where $a$ and $b$ are in $\nats$. Putting on our third-grader hat of course the solution to $b = a+x$ is $x = b-a$. So we'll call this solution "b minus a". Our goal in this post is to give a constructive characterization for subtraction.

There's a hitch: whereas sums and products of natural numbers always exist, differences do not; $5 - 2 = 3$ is a natural number, but $5 - 7 = ?$ is not. So the signature of minus cannot be $\nats \times \nats \rightarrow \nats$. What is it then? How should we handle this?

I can think of three options. First, we can just declare that $b-a$ is not defined if the difference is not a natural number. The corresponding algorithm would then just error out. This should be avoided if possible.

The second option is to implement so-called *truncated subtraction*, so that anytime $b-a$ is not a natural number we simply call it 0. This also is not ideal, since now $b-a$ always exists, but the equation $b = a + (b-a)$ is no longer an identity and we cannot tell just from the value of $b-a$ whether it holds or not.

The third option is a blend of the first two. We can attach an extra element to $\nats$, say $\ast$, and then say $b-a = \ast$ if $b-a$ is not a natural number. This allows us to distinguish when $b-a$ does not exist but keeps the minus function total. So our signature for minus will be $$\nats \times \nats \rightarrow 1 + \nats,$$ where $1 = \{\ast\}$.

:::::: definition ::
Define maps $\varphi : \nats \rightarrow 1 + \nats$ by
$$\varphi(x) = \left\{\begin{array}{ll}
 \rgt(\zero) & \mathrm{if}\ x == \zero \\
 \lft(\ast) & \mathrm{otherwise};
\end{array}\right.$$
$\beta : \nats \times \nats \rightarrow \bool$ by
$$\beta(a,b) = \left\{\begin{array}{ll}
 \btrue & \mathrm{if}\ b = \zero \\
 \bfalse & \mathrm{otherwise};
\end{array}\right.$$
$\psi : \nats \times \nats \rightarrow 1 + \nats$ by $$\psi(a,b) = \rgt(\next(a));$$ and $\omega : \nats \times \nats \rightarrow \nats$ by $$\omega(a,b) = \prev(b).$$

Now define $\nminus : \nats \times \nats \rightarrow 1 + \nats$ by $$\nminus = \bailrec{\varphi}{\beta}{\psi}{\omega}.$$

In Haskell:

> minus :: (Natural n) => n -> n -> Union () n
> minus = bailoutRec phi beta psi omega
>   where
>     phi x = if isZero x
>       then rgt zero
>       else lft ()
> 
>     beta _ b = isZero b
> 
>     psi a _ = rgt (next a)
> 
>     omega _ b = prev b

::::::::::::::::::::

Woo! Since $\nminus$ is defined in terms of bailout recursion, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-minus-up}[]{#cor-minus-up-zero}[]{#cor-minus-up-next}
$\nminus$ is the unique map $f : \nats \times \nats \rightarrow 1 + \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(\zero,b) = \bif{\iszero(b)}{\rgt(\zero)}{\lft(\ast)} \\
 f(\next(a),b) = \bif{\iszero(b)}{\rgt(\next(a))}{\nminus(a,\prev(b))}.
\end{array}\right.$$

::: test :::::::::::

> _test_minus_zero_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_minus_zero_left _ =
>   testName "minus(0,b) == if(isZero(b),rgt(0),lft(*))" $
>   \b -> if eq (isZero b) true
>     then eq (minus zero b) (rgt zero)
>     else eq (minus zero b) (lft ())
> 
> 
> _test_minus_next_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_next_left _ =
>   testName
>     "minus(next(a),b) == if(isZero(b),rgt(next(a)),minus(a,prev(b)))" $
>   \a b -> if eq (isZero b) true
>     then eq (minus (next a) b) (rgt (next a))
>     else eq (minus (next a) b) (minus a (prev b))

::::::::::::::::::::
::::::::::::::::::::

Here are some special cases:

:::::: theorem :::::
[]{#thm-minus-nat-zero}[]{#thm-minus-zero-next}
For all $n \in \nats$ we have the following.

1. $\nminus(n,\zero) = \rgt(n)$.
2. $\nminus(\zero,\next(n)) = \lft(\ast)$.

::: proof ::::::::::
1. If $n = \zero$, then
$$\begin{eqnarray*}
 &   & \nminus(\zero,\zero) \\
 &     \href{@minus@#cor-minus-up-zero}
   = & \bif{\iszero(\zero)}{\rgt(\zero)}{\lft(\ast)} \\
 &     \href{@unary@#thm-iszero-zero}
   = & \bif{\btrue}{\rgt(\zero)}{\lft(\ast)} \\
 &     \href{@booleans@#cor-if-true}
   = & \rgt(\zero)
\end{eqnarray*}$$
as claimed. If $n = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \nminus(\next(m),\zero) \\
 &     \href{@minus@#cor-minus-up-next}
   = & \bif{\iszero(\zero)}{\rgt(\next(m))}{\nminus(m,\prev(\zero))} \\
 &     \href{@unary@#thm-iszero-zero}
   = & \bif{\btrue}{\rgt(\next(m))}{\nminus(m,\prev(\zero))} \\
 &     \href{@booleans@#cor-if-true}
   = & \rgt(\next(m))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \nminus(\zero,\next(n)) \\
 &     \href{@minus@#cor-minus-up-zero}
   = & \bif{\iszero(\next(n))}{\rgt(\zero)}{\lft(\ast)} \\
 &     \href{@unary@#thm-iszero-next}
   = & \bif{\bfalse}{\rgt(\zero)}{\lft(\ast)} \\
 &     \href{@booleans@#cor-if-false}
   = & \lft(\ast)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_nat_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_minus_nat_zero _ =
>   testName "minus(n,0) == rgt(n)" $
>   \n -> eq (minus n zero) (rgt n)
> 
> 
> _test_minus_zero_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_minus_zero_next _ =
>   testName "minus(0,next(n)) == lft(ast)" $
>   \n -> eq (minus zero (next n)) (lft ())

::::::::::::::::::::
::::::::::::::::::::

We can "cancel" $\next$s on both arguments of a $\nminus$.

:::::: theorem :::::
[]{#thm-minus-next-cancel}
Let $a,b \in \nats$. Then we have $$\nminus(\next(b),\next(a)) = \nminus(b,a).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \nminus(\next(b),\next(a)) \\
 &     \href{@minus@#cor-minus-up-next}
   = & \bif{\iszero(\next(a))}{\rgt(\next(b))}{\nminus(b,\prev(\next(a)))} \\
 &     \href{@unary@#thm-iszero-next}
   = & \bif{\bfalse}{\rgt(\next(b))}{\nminus(b,\prev(\next(a)))} \\
 &     \href{@booleans@#cor-if-false}
   = & \nminus(b,\prev(\next(a))) \\
 &     \href{@unary@#thm-prev-next}
   = & \nminus(b,a)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_next_next :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_next_next _ =
>   testName "minus(next(b),next(a)) == minus(b,a)" $
>   \a b -> eq (minus (next b) (next a)) (minus b a)

::::::::::::::::::::
::::::::::::::::::::

Another important special case.

:::::: theorem :::::
[]{#thm-minus-next-self}
Let $a \in \nats$. Then we have $$\nminus(a,\next(a)) = \lft(\ast).$$

::: proof ::::::::::
We proceed by induction on $a$. For the base case $a = \zero$ we have
$$\begin{eqnarray*}
 &   & \nminus(\zero,\next(\zero)) \\
 &     \href{@minus@#thm-minus-zero-next}
   = & \lft(\ast)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $a$; now
$$\begin{eqnarray*}
 &   & \nminus(\next(a),\next(\next(a))) \\
 &     \href{@minus@#thm-minus-next-cancel}
   = & \nminus(a,\next(a)) \\
 &     \hyp{\nminus(a,\next(a)) = \lft(\ast)}
   = & \lft(\ast)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_nat_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_minus_nat_next _ =
>   testName "minus(a,next(a)) == lft(*)" $
>   \a -> eq (minus a (next a)) (lft ())

::::::::::::::::::::
::::::::::::::::::::

The next result shows that $\nminus$ gives a solution to the equation $b = \nplus(a,x)$.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then the following are equivalent.

1. $\nminus(b,a) = \rgt(c)$.
2. $b = \nplus(a,c)$.

::: proof ::::::::::
First we show (1) implies (2) by induction on $b$. For the base case, suppose we have $\nminus(\zero,a) = \rgt(c)$. Now
$$\begin{eqnarray*}
 &   & \rgt(c) \\
 &     \hyp{\nminus(\zero,a) = \rgt(c)}
   = & \nminus(\zero,a) \\
 &     \href{@minus@#cor-minus-up-zero}
   = & \bif{\iszero(a)}{\rgt(\zero)}{\lft(\ast)}
\end{eqnarray*}$$
as needed. If $\iszero(a) = \bfalse$, we have $\rgt(c) = \lft(\ast)$, which is absurd. So $\iszero(a) = \btrue$, and thus $a = \zero$, and moreover $\rgt(c) = \rgt(\zero)$, so $c = \zero$. Then $\zero = \nplus(a,c)$ as needed. For the inductive step, suppose the result holds for all $a$ and $c$ for some $b$, and suppose further that $\nminus(\next(b),a) = \rgt(c)$. If $a = \zero$, we have
$$\begin{eqnarray*}
 &   & \rgt(c) \\
 &     \hyp{\nminus(\next(b),a) = \rgt(c)}
   = & \nminus(\next(b),\zero) \\
 &     \href{@minus@#thm-minus-nat-zero}
   = & \rgt(\next(b))
\end{eqnarray*}$$
so that $\next(b) = c = \nplus(c,\zero)$ as needed. Suppose instead that $a = \next(d)$ for some $d$. Now
$$\begin{eqnarray*}
 &   & \rgt(c) \\
 &     \hyp{\nminus(\next(b),a) = \rgt(c)}
   = & \nminus(\next(b),a) \\
 &     \hyp{a = \next(d)}
   = & \nminus(\next(b),\next(d)) \\
 &     \href{@minus@#thm-minus-next-cancel}
   = & \nminus(b,d)
\end{eqnarray*}$$
and thus $\nplus(d,c) = b$. But then
$$\begin{eqnarray*}
 &   & \next(b) \\
 &     \hyp{b = \nplus(d,c)}
   = & \next(\nplus(d,c)) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \nplus(\next(d),c) \\
 &     \hyp{a = \next(d)}
   = & \nplus(a,c)
\end{eqnarray*}$$
as needed.

Next we show that (2) implies (1) by induction on $a$. For the base case $a = \zero$, if $b = \nplus(a,c) = c$ then $\nminus(b,\zero) = b = c$ as needed. For the inductive step, suppose the implication holds for all $b$ and $c$ for some $a$. In particular, if $\nplus(a,c) = b$, then $\nminus(b,a) = \rgt(c)$. Suppose further that $b = \nplus(\next(a),c)$. Now $b = \next(\nplus(a,c)) = \next(d)$ for some $d$, where $\nminus(d,a) = \rgt(c)$. Then we have
$$\begin{eqnarray*}
 &   & \nminus(b,\next(a)) \\
 &     \hyp{b = \next(\nplus(a,c))}
   = & \nminus(\next(\nplus(a,c)),\next(a)) \\
 &     \href{@minus@#thm-minus-next-cancel}
   = & \nminus(\nplus(a,c),a) \\
 &     \hyp{d = \nplus(a,c)}
   = & \nminus(d,a) \\
 &     \hyp{\nminus(d,a) = \rgt(c)}
   = & \rgt(c)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_plus_equiv :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_minus_plus_equiv _ =
>   testName "(minus(b,a) == rgt(c)) == (plus(a,c) == b)" $
>   \a b c -> eq
>     (eq (minus b a) (rgt c))
>     (eq (plus a c) b)

::::::::::::::::::::
::::::::::::::::::::

Now $\nminus$ inherits several properties from $\nplus$. For instance, $\nminus$ is cancellative.

:::::: theorem :::::
Let $a,b,c \in \nats$. Then the following are equivalent.

1. If $\nminus(b,a) = \nminus(b,c)$ and $\isRgt(\nminus(b,a)) = \btrue$, then $a = c$.
2. If $\nminus(a,b) = \nminus(c,b)$ and $\isRgt(\nminus(a,b)) = \btrue$, then $a = c$.

::: proof ::::::::::
1. Say $$\nminus(b,a) = \rgt(d) = \nminus(b,c).$$ Now $$\nplus(a,d) = b = \nplus(c,d)$$ and thus $a = c$ as claimed.
2. Say $$\nminus(a,b) = \rgt(d) = \nminus(c,b).$$ Now $$a = \nplus(b,d) = c$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_cancellative_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_minus_cancellative_left _ =
>   testName "if minus(b,a) == minus(b,c) == rgt(d) then a == c" $
>   \a b c -> if and (eq (minus b a) (minus b c)) (isRgt (minus b a))
>     then eq a c
>     else true
> 
> 
> _test_minus_cancellative_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_minus_cancellative_right _ =
>   testName "if minus(a,b) == minus(c,b) == rgt(d) then a == c" $
>   \a b c -> if and (eq (minus a b) (minus c b)) (isRgt (minus a b))
>     then eq a c
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\nminus$ "undoes" $\nplus$.

:::::: theorem :::::
[]{#thm-minus-plus-left}[]{#thm-minus-plus-right}
Let $a,b \in \nats$. Then we have the following.

1. $\nminus(\nplus(b,a),b) = \rgt(a)$.
2. $\nminus(\nplus(a,b),b) = \rgt(a)$.

::: proof ::::::::::
1. We have $\nplus(b,a) = \nplus(b,a)$, so that $\nminus(\nplus(b,a),b) = \rgt(a)$ as claimed.
2. We have $$\nminus(\nplus(a,b),b) = \nminus(\nplus(b,a),b) = \rgt(a)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_plus_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_plus_right _ =
>   testName "minus(plus(b,a),b) == rgt(a)" $
>   \a b -> eq (minus (plus b a) b) (rgt a)
> 
> 
> _test_minus_plus_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_plus_left _ =
>   testName "minus(plus(a,b),b) == rgt(a)" $
>   \a b -> eq (minus (plus a b) b) (rgt a)

::::::::::::::::::::
::::::::::::::::::::

We are able to rearrange $\nminus$ expressions (a little bit).

:::::: theorem :::::
Let $a,b,c,d \in \nats$. Then the following hold.

1. If $\nminus(b,a) = \rgt(c)$, then $\nminus(\next(b),a) = \rgt(\next(c))$.
2. If $\nminus(b,a) = \rgt(c)$, then $\nminus(b,c) = \rgt(a)$.
3. If $\nminus(b,a) = \rgt(c)$, then $\nminus(\nplus(b,d),a) = \rgt(\nplus(c,d))$.

::: proof ::::::::::
1. Since $\nminus(b,a) = \rgt(c)$, we have $\nplus(a,c) = b$, so that $$\nplus(a,\next(c)) = \next(\nplus(a,c)) = \next(b).$$ Thus we have $$\nminus(\next(b),a) = \rgt(\next(c))$$ as claimed.
2. Since $\nminus(b,a) = \rgt(c)$, we have $b = \nplus(a,c) = \nplus(c,a)$, so that $\nminus(b,c) = \rgt(a)$ as claimed.
3. Suppose $\nminus(b,a) = \rgt(c)$; then $b = \nplus(a,c)$. Now $$\nplus(b,d) = \nplus(\nplus(a,c),d) = \nplus(a,\nplus(c,d)),$$ so that $$\nminus(\nplus(b,d),a) = \rgt(\nplus(c,d))$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_next_left_cond :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_next_left_cond _ =
>   testName "if minus(b,a) == rgt(c) then minus(next(b),a) == rgt(next(c))" $
>   \a b -> case minus b a of
>     Right c -> eq (minus (next b) a) (rgt (next c))
>     Left () -> true
> 
> 
> _test_minus_swap :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_swap _ =
>   testName "if minus(b,a) == rgt(c) then minus(b,c) == rgt(a)" $
>   \a b -> case minus b a of
>     Right c -> eq (minus b c) (rgt a)
>     Left () -> true
> 
> 
> _test_minus_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_minus_plus _ =
>   testName "if minus(b,a) == rgt(c) then minus(plus(b,d),a) == rgt(plus(c,d))" $
>   \a b d -> case minus b a of
>     Right c -> eq (minus (plus b d) a) (rgt (plus c d))
>     Left () -> true

::::::::::::::::::::
::::::::::::::::::::

Given natural numbers $a$ and $b$, either $\nminus(a,b)$ or $\nminus(b,a)$ is of the form $\rgt(c)$ for some $c$.

:::::: theorem :::::
Let $a,b \in \nats$. If $\nminus(a,b) = \lft(\ast)$, then $\nminus(b,a) = \rgt(c)$ for some $c$.

::: proof ::::::::::
We proceed by induction on $a$. For the base case $a = \zero$, if $\nminus(\zero,b) = \lft(\ast)$ we have $b \neq \zero$ and $\nminus(b,\zero) = \rgt(b)$ as needed.

For the inductive step, suppose the implication holds for all $b$ for some $a$. Suppose further that $\nminus(\next(a),b) = \lft(\ast)$. If $b = \zero$, note that $\nminus(\next(a),\zero) = \lft(\zero)$ is false, so the implication holds vacuously. If $b = \next(d)$ for some $d$, then we have $$\lft(\ast) = \nminus(\next(a),b) = \nminus(\next(a),\next(d)) = \nminus(a,d).$$ By the induction hypothesis we have $$\nminus(d,a) = \rgt(c)$$ for some $c$, so that $$\nminus(b,a) = \nminus(\next(d),a) = \rgt(\next(c))$$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_flip :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_minus_flip _ =
>   testName "if minus(a,b) == lft(*) then isRgt(minus(b,a))" $
>   \a b -> if eq (minus a b) (lft ())
>     then isRgt (minus b a)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\ntimes$ distributes over $\nminus$.

:::::: theorem :::::
Let $a,b,c \in \nats$. If $\nminus(a,b) = \rgt(d)$ for some $d \in \nats$, then $$\nminus(\ntimes(c,a),\ntimes(c,b)) = \rgt(\ntimes(c,d)).$$

::: proof ::::::::::
We proceed by induction on $a$. For the base case $a = \zero$, suppose we have $\nminus(\zero,b) = \rgt(d)$; then $d = \zero$ and $b = \zero$. Now
$$\begin{eqnarray*}
 &   & \nminus(\ntimes(c,a),\ntimes(c,b)) \\
 &     \let{a = \zero}
   = & \nminus(\ntimes(c,\zero),\ntimes(c,b)) \\
 &     \href{@times@#thm-times-zero-right}
   = & \nminus(\zero,\ntimes(c,b))
 &     \let{b = \zero}
   = & \nminus(\zero,\ntimes(c,\zero)) \\
 &     \href{@times@#thm-times-zero-right}
   = & \nminus(\zero,\zero) \\
 &     \href{@minus@#thm-minus-nat-zero}
   = & \rgt(\zero)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \rgt(\ntimes(c,d)) \\
 &     \let{d = \zero}
   = & \rgt(\ntimes(c,\zero)) \\
 &     \href{@times@#thm-times-zero-right}
   = & \rgt(\zero)
\end{eqnarray*}$$
as claimed.

For the inductive step, suppose the equality holds for some $a \in \nats$ and suppose that $\nminus(\next(a),b) = \rgt(d)$. Then we have
$$\begin{eqnarray*}
 &   & \nminus(\ntimes(c,\next(a)),\ntimes(c,b)) \\
 &     \href{@times@#thm-times-next-right}
   = & \nminus(\nplus(\ntimes(c,a),c),\ntimes(c,b)) \\
 & = & \nplus(\nminus(\ntimes(c,a),\ntimes(c,b)),c) \\
 & = & \nplus(\ntimes(c,\nminus(a,b)),c) \\
 &     \href{@times@#thm-times-next-right}
   = & \ntimes(c,\next(\nminus(a,b))) \\
 & = & \ntimes(c,\nminus(\next(a),b))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_minus_times_dist_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_minus_times_dist_left _ =
>   testName "if (minus(a,b) == rgt(d)) then minus(times(c,a),times(c,b)) == rgt(times(c,d))" $
>   \a b c -> case (minus a b) of
>     Right d -> eq
>       (minus (times c a) (times c b))
>       (rgt (times c d))
>     Left () -> true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

> _test_minus ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_minus n size cases = do
>   testLabel1 "minus" n
>   let args = testArgs size cases
> 
>   runTest args (_test_minus_zero_left n)
>   runTest args (_test_minus_next_left n)
>   runTest args (_test_minus_nat_zero n)
>   runTest args (_test_minus_zero_next n)
>   runTest args (_test_minus_next_next n)
>   runTest args (_test_minus_nat_next n)
>   runTest args (_test_minus_plus_equiv n)
>   runTest args (_test_minus_cancellative_left n)
>   runTest args (_test_minus_cancellative_right n)
>   runTest args (_test_minus_plus_right n)
>   runTest args (_test_minus_plus_left n)
>   runTest args (_test_minus_next_left_cond n)
>   runTest args (_test_minus_swap n)
>   runTest args (_test_minus_plus n)
>   runTest args (_test_minus_flip n)
>   runTest args (_test_minus_times_dist_left n)

Main:

> main_minus :: IO ()
> main_minus = do
>   _test_minus (zero :: Unary) 30 50
