---
title: The Division Algorithm
author: nbloomf
date: 2017-04-08
tags: arithmetic-made-difficult, literate-haskell
slug: divalg
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DivisionAlgorithm
>   ( divalg, quo, rem, _test_divalg, main_divalg
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
> import SimpleRecursion
> import Plus
> import Times
> import LessThanOrEqualTo

Finally we come to the first power tool for natural numbers: the division algorithm. Remember this theorem states that given any two natural numbers $a$ and $b$, with $b \neq \zero$, there is a *unique* pair of natural numbers $(q,r)$ such that $a = qb+r$ and $r$ is not "too big", specifically, $r < b$; this $q$ is called the *quotient* of $a$ by $b$, and $r$ is the *remainder*.

I like this result for several reasons. It ties together the three basic operations on $\nats$ -- $\next$, $\nplus$, and $\ntimes$ -- in a satisfying way, and it has two conclusions, one an equality and the other an inequality. It also has some really powerful applications. Notably, we'll use the division algorithm to compute greatest common divisors and to compute fixed-radix representations of numbers.

The task at hand is to find a constructive, or more precisely, simple recursive, definition for the division algorithm. This function takes a pair of natural numbers $(a,b)$ and returns a pair of natural numbers $(q,r)$, so its signature should be something like $$\nats \times \nats \rightarrow \nats \times \nats.$$ Remember that the signature of $\simprec{\varphi}{\mu}$ is $$\nats \times A \rightarrow B,$$ where $\varphi : A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Letting $A = \nats$ and $B = \nats \times \nats$, we're looking for $$\varphi : \nats \rightarrow \nats \times \nats$$ and $$\mu : \nats \times \nats \times (\nats \times \nats) \rightarrow \nats \times \nats$$ so that $\Theta = \simprec{\varphi}{\mu}$ acts like the division algorithm. But how does the division algorithm act?

For starters, we have $$\Theta(\zero,b) = \varphi(b) = (q,r)$$ where $$\zero = \nplus(\ntimes(q,b),r).$$ So $r = q = \zero$; evidently then $\varphi(x) = (\zero,\zero)$ for all $x$.

Suppose now that $\Theta(a,b) = (q,r)$. Can we describe $\Theta(\next(a),b)$ in terms of $q$ and $r$? (Presumably yes.) Switching to more familiar notation for a moment, we have $$a = qb+r,$$ so that $$a+1 = qb+r+1.$$ So $q$ and $r+1$ satisfy the equality constraint, but possibly not the inequality constraint. If $r+1 < b$, then $q$ and $r+1$ are quotient and remainder for $a+1$ and $b$. But what if $r+1 \geq b$? Well, this failure is too general; since $r < b$, the worst that can happen is $r+1 = b$. But in this case we can "increment" $q$ and "reset" $r$ to $\zero$; that is, $q+1$ and $\zero$ are quotient and remainder for $a+1$ and $b$. So in $$\Theta(\next(a),b) = \mu(a,b,(q,r))$$ (where $(q,r) = \Theta(a,b)$), we want $\mu(a,b,(q,r)) = (q+1,\zero)$ if $r+1 = b$ and $(q,r+1)$ otherwise.

Let's try it.

:::::: definition ::
Define $\varphi : \nats \rightarrow \nats \times \nats$ by $\varphi(x) = (\zero,\zero)$, and define $\mu : \nats \times \nats \times (\nats \times \nats) \rightarrow \nats \times \nats$ by
$$\mu(a,b,(q,r)) = \left\{\begin{array}{ll}
 (\next(q),\zero) & \mathrm{if}\ b = \next(r) \\
 (q,\next(r)) & \mathrm{otherwise}.
\end{array}\right.$$
Then define $\ndivalg : \nats \times \nats \rightarrow \nats \times \nats$ by $$\ndivalg = \simprec{\varphi}{\mu}.$$ We also define helpers $\nquo, \nrem : \nats \times \nats \rightarrow \nats$ by $$\nquo(a,b) = \fst(\ndivalg(a,b))$$ and $$\nrem(a,b) = \snd(\ndivalg(a,b)).$$

In Haskell:

> divalg :: (Natural n, Equal n) => n -> n -> (n,n)
> divalg = simpleRec phi mu
>   where
>     phi _ = (zero, zero)
>     mu _ b (q,r) = if eq b (next r)
>       then (next q, zero)
>       else (q, next r)
> 
> 
> quo :: (Natural n, Equal n) => n -> n -> n
> quo a b = fst (divalg a b)
> 
> 
> rem :: (Natural n, Equal n) => n -> n -> n
> rem a b = snd (divalg a b)

::::::::::::::::::::

Since $\ndivalg$ is defined in terms of simple recursion, it is the unique solution to a system of functional equations.

:::::: corollary :::
$\ndivalg$ is the unique map $f : \nats \times \nats \rightarrow \nats \times \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(\zero,b) = (\zero,\zero) \\
 f(\next(a),b) = \bif{\beq(b,\next(r))}{(\next(q),\zero)}{(q,\next(r))}\ \mathrm{where}\ (q,r) = f(q,r).
\end{array}\right.$$

::: test :::::::::::

> _test_divalg_zero_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_divalg_zero_left _ =
>   testName "divalg(0,a) = (0,0)" $
>   \a -> eq (divalg zero a) (zero, zero)
> 
> 
> _test_divalg_next_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_next_left _ =
>   testName "divalg(next(a),b) == if(eq(b,next(r)),(next(q),0),(q,next(r)))" $
>   \a b -> let (q,r) = divalg a b in
>     eq
>       (divalg (next a) b)
>       (if (eq b (next r)) then (next q, zero) else (q, next r))
> 
> 
> _test_divalg_quo :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_quo _ =
>   testName "quo(a,b) = q where (q,_) = divalg(a,b)" $
>   \a b -> let (q,_) = divalg a b in
>   eq q (quo a b)
> 
> 
> _test_divalg_rem :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_rem _ =
>   testName "rem(a,b) = r where (_,r) = divalg(a,b)" $
>   \a b -> let (_,r) = divalg a b in
>   eq r (rem a b)

::::::::::::::::::::
::::::::::::::::::::

Now $\ndivalg(a,b)$ acts like the division algorithm.

:::::: theorem :::::
Let $a,b \in \nats$ and let $(q,r) = \ndivalg(a,\next(b))$. Then we have the following.

1. $a = \nplus(\ntimes(q,\next(b)),r)$.
2. $\nleq(r,b) = \btrue$.

::: proof ::::::::::
We proceed by induction on $a$. For the base case, $a = \zero$, note that $$\ndivalg(\zero,\next(b)) = \varphi(\next(b)) = (\zero,\zero).$$ Now we have $$\nplus(\ntimes(\zero,\next(b)),\zero) = \zero = a$$ and $\nleq(\zero,\next(b))$ as needed.

For the inductive step, suppose both conclusions hold for all $b$ for some $a$. Let $(q_1,r_1) = \ndivalg(a,b)$. Now we have $$\begin{eqnarray*} & & \ndivalg(\next(a),\next(b)) \\ & = & \mu(a,\next(b),\ndivalg(a,\next(b))) \\ & = & \mu(a,\next(b),(q_1,r_1)) \\ & = & Q. \end{eqnarray*}$$ We have two possibilities: either $\next(r_1) = \next(b)$ or $\next(r_1) \neq \next(b)$.

Suppose first that $\next(r_1) = \next(b)$; then we have $$Q = (\next(q_1),\zero).$$ Now we have $$\begin{eqnarray*} & & \nplus(\ntimes(\next(q_1),\next(b)),\zero) \\ & = & \ntimes(\next(q_1),\next(b)) \\ & = & \nplus(\ntimes(q_1,\next(b)),\next(b)) \\ & = & \nplus(\ntimes(q_1,\next(b)),\next(r_1)) \\ & = & \next(\nplus(\ntimes(q_1,\next(b)),r_1)) \\ & = & \next(a) \end{eqnarray*}$$ as needed; moreover, we have $\nleq(\zero,b) = \btrue$.

Now suppose we have $\next(r_1) \neq \next(b)$. Now we have $$Q = (q_1,\next(r_1)).$$ In this case,
$$\begin{eqnarray*}
 &   & \nplus(\ntimes(q_1,\next(b)),\next(r_1)) \\
 & = & \next(\nplus(\ntimes(q_1,\next(b)),r_1)) \\
 & = & \next(a).
\end{eqnarray*}$$
If $\nleq(\next(r_1),b) = \bfalse$, then $\nleq(b,\next(r_1)) = \btrue$ and $\next(r_1) \neq b$. In particular, we must have $r_1 = b$. But then $\next(r_1) = \next(b)$, a contradiction. So we must have $\nleq(\next(r_1),b) = \btrue$, and the conclusion holds for all $b$ given $\next(a)$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_divalg_equality :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_equality _ =
>   testName "a == plus(times(q,b),r) where (q,r) = divalg(a,b)" $
>   \a b -> let (q,r) = divalg a b in
>   eq a (plus (times q b) r)
> 
> 
> _test_divalg_inequality :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_inequality _ =
>   testName "leq(r,b) where (_,r) = divalg(a,next(b))" $
>   \a b -> let (_,r) = divalg a (next b) in
>   leq r b

::::::::::::::::::::
::::::::::::::::::::

Also the output of the division algorithm is unique.

:::::: theorem :::::
Let $a,b \in \nats$ and suppose we have $q,r \in \nats$ such that $$a = \nplus(\ntimes(q,\next(b)),r)$$ and $\nleq(r,b) = \btrue$. Then $(q,r) = \ndivalg(a,b)$.

::: proof ::::::::::
It suffices to show that if $(q_1,r_1)$ and $(q_2,r_2)$ both satisfy the conditions of the division algorithm, then $q_1 = q_2$ and $r_1 = r_2$. To this end, suppose we have $$\begin{eqnarray*} & & \nplus(\ntimes(q_1,\next(b)),r_1) \\ & = & a \\ & = & \nplus(\ntimes(q_2,\next(b)),r_2). \end{eqnarray*}$$ Without loss of generality, we have $\nleq(r_1,r_2)$; say $r_2 = \nplus(r_1,k)$. Now $$\begin{eqnarray*} & & \nplus(\ntimes(q_1,\next(b)),r_1) \\ & = & \nplus(\ntimes(q_2,\next(b)),r_2) \\ & = & \nplus(\ntimes(q_2,\next(b)),\nplus(r_1,k))) \\ & = & \nplus(\nplus(\ntimes(q_2,\next(b)),k),r_1), \end{eqnarray*}$$ and thus $$\ntimes(q_1,\next(b)) = \nplus(\ntimes(q_2,\next(b)),k).$$ Note that $\nleq(k,r_2)$, and thus $\nleq(k,b)$.

We wish to show that $k = \zero$. To this end, let $P(q_1,q_2,b,k)$ denote the statement $$\mathrm{if}\ \ntimes(q_1,\next(b)) = \nplus(\ntimes(\ntimes(q_2,\next(b))),k)\ \mathrm{then}\ k = \zero,$$ and define a set $$M = \{ q_1 \in \nats \mid \forall q_2,b,k\ P(q_1,q_2,b,k) \}.$$ We will show that $M = \nats$ by (you guessed it!) induction.

For the base case $q_1 = \zero$, suppose the hypothesis of $P(\zero,q_2,b,k)$. Then we have $$\zero = \ntimes(\zero,\next(b)) = \nplus(\ntimes(q_2,\next(b)),k),$$ so that $k = \zero$. For the inductive step, we suppose that $q_1 \in M$. Now define the set $$N(x) = \{ q_2 \in \nats \mid \forall b,k, P(x,q_2,b,k) \};$$ we have supposed that $N(q_1) = \nats$.

We will show that $N(\next(q_1)) = \nats$ also by induction. For the base case $q_2 = \zero$, suppose the hypothesis of $P(\next(q_1),\zero,b,k)$. Now $$\begin{eqnarray*} & & \nplus(\ntimes(q_1,\next(b)),\next(b)) \\ & = & \ntimes(\next(q_1),\next(b)) \\ & = & \nplus(\ntimes(\zero,\next(b)),k) \\ & = & \nplus(\zero,k) \\ & = & k. \end{eqnarray*}$$ Thus $\nleq(\next(b),k)$. But now we have $\nleq(\next(b),b)$ by transitivity, a contradiction. Thus the hypothesis of $P(\next(q_1),\zero,b,k)$ is false, and we have $\zero \in N(\next(q_1))$ vacuously.

For the inductive step, suppose we have $q_2 \in N(\next(q_1))$, and suppose the hypothesis of $P(\next(q_1),\next(q_2),b,k)$; that is, that $$\ntimes(\next(q_1),\next(b)) = \nplus(\ntimes(\next(q_2),\next(b)),k).$$ Now we have
$$\begin{eqnarray*}
 &   & \nplus(\ntimes(q_1,\next(b)),\next(b)) \\
 & = & \ntimes(\next(q_1),\next(b)) \\
 & = & \nplus(\ntimes(\next(q_2),\next(b)),k) \\
 & = & \nplus(\nplus(\ntimes(q_2,\next(b)),\next(b)),k) \\
 & = & \nplus(\nplus(\ntimes(q_2,\next(b)),k),\next(b))
\end{eqnarray*}$$
So we have $$\ntimes(q_1,\next(b)) = \nplus(\ntimes(q_2,\next(b)),k),$$ and since $N(q_1) = \nats$, $k = \zero$. So $\next(q_2) \in N(\next(q_1))$ as needed.

So we have $k = \zero$, and thus $$\ntimes(q_1,\next(b)) = \ntimes(q_2,\next(b)).$$ Thus $q_1 = q_2$, and moreover $r_1 = r_2$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_divalg_unique :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> n -> Bool)
> _test_divalg_unique _ =
>   testName "if and(eq(a,plus(times(q,next(b)),r),leq(r,b)) then (q,r) = divalg(a,b)" $
>   \a b q r -> if and (eq a (plus (times q (next b)) r)) (leq r b)
>     then eq (q,r) (divalg a (next b))
>     else true

::::::::::::::::::::
::::::::::::::::::::

The last two theorems say that the output of $\ndivalg(a,b)$ is the unique solution of a particular system of equations so long as $b$ is not $\zero$. But what if $b$ is zero? We frankly won't usually be interested in this case, but it will show up later as the base case in some induction proofs. Of course in the $b = \zero$ case the output of $\ndivalg$ is no longer a unique solution to the system of equations, and the particular solution is a quirk of our definition.

:::::: theorem :::::
If $a \in \nats$ we have the following.

1. $\ndivalg(a,\zero) = (\zero,a)$.
2. $\ndivalg(a,\next(\zero)) = (a,\zero)$.
3. If $\nleq(a,b)$, then $\ndivalg(a,\next(b)) = (\zero,a)$.
4. $\ndivalg(\next(a),\next(a)) = (\next(\zero),\zero)$.

::: proof ::::::::::
1. We proceed by induction on $a$. For the base case $a = \zero$, note that $$\ndivalg(\zero,\zero) = (\zero, \zero)$$ as needed. For the inductive step, suppose the equation holds for some $a$. Now
$$\begin{eqnarray*}
 &   & \ndivalg(\next(a),\zero) \\
 & = & \bif{\beq(\zero,\next(r))}{(\next(q),\zero)}{(q,\next(r))}\ \mathrm{where}\ (q,r) = \ndivalg(a,\zero) \\
 & = & \bif{\beq(\zero,\next(a))}{(\next(\zero),\zero)}{(\zero,\next(a))} \\
 & = & \bif{\bfalse}{(\next(\zero),\zero)}{(\zero,\next(a))} \\
 & = & (\zero, \next(a))
\end{eqnarray*}$$
as needed.
2. Note that $a = \nplus(\ntimes(a,\next(\zero)),\zero)$ and $\nleq(\zero,\zero)$. By the uniqueness of quotients and remainders for nonzero divisors, we have $\ndivalg(a,\next(\zero)) = (a,\zero)$ as claimed.
3. Note that $a = \nplus(\ntimes(\zero,\next(b)),a)$ and $\nleq(a,b)$. By the uniqueness of quotients and remainders for positive divisors we have $\ndivalg(a,\next(b)) = (\zero,a)$.
4. Note that
$$\begin{eqnarray*}
 &   & \nplus(\ntimes(\next(\zero),a),\zero) \\
 & = & \nplus(\next(a),\zero) \\
 & = & \next(a).
\end{eqnarray*}$$
Since $\next(a) \neq \zero$, by the uniqueness of the division algorithm, we have $\ndivalg(\next(a),\next(a)) = (\next(\zero),\zero)$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_divalg_zero_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_divalg_zero_right _ =
>   testName "divalg(a,0) = (0,a)" $
>   \a -> eq (divalg a zero) (zero, a)
> 
> 
> _test_divalg_one_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_divalg_one_right _ =
>   testName "divalg(a,next(0)) = (a,0)" $
>   \a -> eq (divalg a (next zero)) (a, zero)
> 
> 
> _test_divalg_leq :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_leq _ =
>   testName "if leq(a,b) then divalg(a,next(b)) = (0,a)" $
>   \a b -> if leq a b
>     then eq (divalg a (next b)) (zero, a)
>     else true
> 
> 
> _test_divalg_self_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_divalg_self_next _ =
>   testName "divalg(next(a),next(a)) == (next(0),0)" $
>   \a -> eq (divalg (next a) (next a)) (next zero, zero)

::::::::::::::::::::
::::::::::::::::::::

$\nquo$ interacts with $\ntimes$.

:::::: theorem :::::
Let $a,b \in \nats$. If $b \neq \zero$, then $\nquo(\ntimes(a,b),b) = a$.

::: proof ::::::::::
Say $b = \next(m)$. Note that $\nleq(\zero,m)$. Now $$\ntimes(a,b) = \nplus(\ntimes(a,b),\zero),$$ and by the uniqueness of quotients by nonzero divisors, we have $a = \nquo(\ntimes(a,b),b)$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_divalg_times_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_divalg_times_left _ =
>   testName "quo(times(a,next(b)),next(b)) = a" $
>   \a b -> eq (quo (times a (next b)) (next b)) a

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite.

> _test_divalg ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_divalg n maxSize numCases = do
>   testLabel1 "divalg" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_divalg_zero_left n)
>   runTest args (_test_divalg_next_left n)
>   runTest args (_test_divalg_quo n)
>   runTest args (_test_divalg_rem n)
>   runTest args (_test_divalg_equality n)
>   runTest args (_test_divalg_inequality n)
>   runTest args (_test_divalg_unique n)
>   runTest args (_test_divalg_zero_right n)
>   runTest args (_test_divalg_one_right n)
>   runTest args (_test_divalg_leq n)
>   runTest args (_test_divalg_self_next n)
>   runTest args (_test_divalg_times_left n)

Main.

> main_divalg :: IO ()
> main_divalg = do
>   _test_divalg (zero :: Unary) 20 100
