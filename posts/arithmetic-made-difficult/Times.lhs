---
title: Multiplication
author: nbloomf
date: 2017-03-31
tags: arithmetic-made-difficult, literate-haskell
---

> module Times
>  ( times, _test_times, main_times
>  ) where
> 
> import Booleans
> import NaturalNumbers
> import Plus
> 
> import Prelude ()
> import Test.QuickCheck

Natural number multiplication has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define it as $\Theta = \simprec{\varphi}{\mu}$ for some appropriate $\varphi$ and $\mu$. Using the universal property of simple recursion and how we want multiplication to behave, note that on the one hand we want $\Theta(\zero,m) = \zero$ for all $m$, while on the other hand we have $\Theta(\zero,m) = \varphi(m)$. So apparently we need $\varphi(m) = \zero$ for all $m$.

Similarly, we want $\Theta(\next(n),m) = \nplus(\Theta(n,m),m)$, but we also have $$\Theta(\next(n),m) = \mu(n,m,\Theta(n,m)).$$ So apparently we need $\mu(n,m,k) = \nplus(k,m)$.

With this in mind, we define a binary operation $\ntimes$ on $\nats$ as follows.

<div class="result">
<div class="defn"><p>
Let $\varphi : \nats \rightarrow \nats$ be given by $\varphi(m) = \zero$, and let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \nplus(b,a)$. We then define $\ntimes : \nats \times \nats \rightarrow \nats$ by $$\ntimes = \simprec{\varphi}{\mu}.$$

In Haskell:

> times :: (Natural t) => t -> t -> t
> times = simpleRec phi mu
>   where
>     phi _ = zero
>     mu _ a b = plus b a

</p></div>
</div>

Showing that $\ntimes$ has the familiar properties of multiplication then comes down to a few applications of induction.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\ntimes(\zero,a) = \zero = \ntimes(a,\zero)$.
2. $\ntimes(\next(\zero),a) = a = \ntimes(a,\next(\zero))$.
3. $\ntimes(\next(a),b) = \nplus(\ntimes(a,b),b)$.
4. $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$.
5. $\ntimes(a,b) = \ntimes(b,a)$.
6. $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$.
7. $\ntimes(\nplus(a,b),c) = \nplus(\ntimes(a,c),\ntimes(b,c))$.
8. $\ntimes(\ntimes(a,b),c) = \ntimes(a,\ntimes(b,c))$.
9. If $\ntimes(\next(a),b) = \ntimes(\next(a),c)$ then $b = c$.
10. If $\ntimes(b,\next(a)) = \ntimes(c,\next(a))$ then $b = c$.
</div>

<div class="proof"><p>
1. Note first that for all $a$, we have $$\ntimes(\zero,a) = \varphi(a) = \zero.$$ We show the second equality by induction on $a$. For the base case, note that $\ntimes(\zero,\zero) = \zero$. For the inductive step, suppose we have $\ntimes(a,\zero) = \zero$ for some $a$. Then $$\begin{eqnarray*} \ntimes(\next(a),\zero) & = & \mu(a,\zero,\ntimes(a,\zero)) \\ & = & \mu(a,\zero,\zero) \\ & = & \nplus(\zero,\zero) \\ & = & \zero \end{eqnarray*}$$ as needed.
2. Note first that for all $a$, we have $$\begin{eqnarray*} \ntimes(\next(\zero),a) & = & \mu(\zero,a,\ntimes(\zero,a)) \\ & = & \mu(\zero,a,\zero) \\ & = & \nplus(\zero,a) \\ & = & a. \end{eqnarray*}$$ We show the second equality by induction on $a$. For the base case, note that $\ntimes(\zero,\next(\zero)) = \zero$. For the inductive step, suppose we have $\ntimes(a,\next(\zero)) = a$ for some $a$. Now $$\begin{eqnarray*} \ntimes(\next(a),\next(\zero)) & = & \mu(a,\next(\zero),\ntimes(a,\next(\zero)) \\ & = & \mu(a,\next(\zero),a) \\ & = & \nplus(a,\next(\zero)) \\ & = & \next(\nplus(a,\zero)) \\ & = & \next(a) \end{eqnarray*}$$ as needed.
3. Note that $$\ntimes(\next(a),b) = \mu(a,b,\ntimes(a,b)) = \nplus(\ntimes(a,b),b)$$ as claimed.
4. We proceed by induction on $a$. For the base case, we have $$\ntimes(\zero,\next(b)) = \zero = \nplus(\zero,\zero) = \nplus(\ntimes(\zero,b),\zero)$$ as needed. For the inductive step, suppose we have $\ntimes(a,\next(b)) = \nplus(\ntimes(a,b),a)$ for some $a$. Now $$\begin{eqnarray*} & & \ntimes(\next(a),\next(b)) \\ & = & \mu(a,\next(b),\ntimes(a,\next(b))) \\ & = & \nplus(\ntimes(a,\next(b)),\next(b)) \\ & = & \next(\nplus(\ntimes(a,\next(b)),b)) \\ & = & \next(\nplus(\nplus(\ntimes(a,b),a),b)) \\ & = & \next(\nplus(\ntimes(a,b),\nplus(a,b))) \\ & = &\next(\nplus(\ntimes(a,b),\nplus(b,a))) \\ & = & \next(\nplus(\nplus(\ntimes(a,b),b),a)) \\ & = & \next(\nplus(\ntimes(\next(a),b),a)) \\ & = & \nplus(\ntimes(\next(a),b), \next(a)) \end{eqnarray*}$$ as needed.
5. We proceed by induction on $a$. For the base case, note that $$\ntimes(\zero,b) = \zero = \ntimes(b,\zero)$$ as needed. For the inductive step, suppose we have $\ntimes(a,b) = \ntimes(b,a)$ for some $a$. Now $$\begin{eqnarray*} \ntimes(\next(a),b) & = & \mu(a,b,\ntimes(a,b)) \\ & = & \mu(a,b,\ntimes(a,b)) \\ & = & \nplus(\ntimes(a,b),b) \\ & = & \nplus(\ntimes(b,a),b) \\ & = & \ntimes(b,\next(a)) \end{eqnarray*}$$ as needed.
6. We proceed by induction on $a$. For the base case, we have $$\ntimes(\zero,\nplus(b,c)) = \zero = \nplus(\zero,\zero) = \nplus(\ntimes(\zero,b),\ntimes(\zero,c))$$ as needed. For the inductive step, suppose we have $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$ for some $a$. Now $$\begin{eqnarray*} & & \ntimes(\next(a),\nplus(b,c)) \\ & = & \nplus(\ntimes(a, \nplus(b,c)), \nplus(b,c)) \\ & = & \nplus(\nplus(\ntimes(a,b),\ntimes(a,c)), \nplus(b,c)) \\ & = & \nplus(\nplus(\nplus(\nplus(\ntimes(a,b),\ntimes(a,c))),b),c) \\ & = & \nplus(\nplus(\ntimes(a,b),\nplus(\ntimes(a,c),b)),c) \\ & = & \nplus(\nplus(\ntimes(a,b),\nplus(b,\ntimes(a,c))),c) \\ & = & \nplus(\nplus(\nplus(\ntimes(a,b),b),\ntimes(a,c)),c) \\ & = & \nplus(\nplus(\ntimes(a,b),b),\nplus(\ntimes(a,c),c)) \\ & = & \nplus(\ntimes(\next(a),b),\ntimes(\next(a),c)) \end{eqnarray*}$$ as needed.
7. Follows from (5) and (6).
8. We proceed by induction on $a$. For the base case, we have $$\begin{eqnarray*} \ntimes(\zero,\ntimes(b,c)) & = & \zero \\ & = & \ntimes(\zero,c) \\ & = & \ntimes(\ntimes(\zero,b),c) \end{eqnarray*}$$ as needed. For the inductive step, suppose we have $\ntimes(a,\ntimes(b,c)) = \ntimes(\ntimes(a,b),c)$ for some $a$. Then $$\begin{eqnarray*} & & \ntimes(\ntimes(\next(a),b),c) \\ & = & \ntimes(\nplus(\ntimes(a,b),b),c) \\ & = & \nplus(\ntimes(\ntimes(a,b),c), \ntimes(b,c)) \\ & = & \nplus(\ntimes(a,\ntimes(b,c)),\ntimes(b,c)) \\ & = & \ntimes(\next(a),\ntimes(b,c)) \end{eqnarray*}$$ as needed.
9. This proof will be a little different: we will use induction twice; first on $b$, and then on $c$. To this end, let $$B = \{ b \in \nats \mid \forall c, \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}$$ and given $b \in \nats$ let $$C(b) = \{ c \in \nats \mid \forall a,\ \mathrm{if}\ \ntimes(\next(a),b) = \ntimes(\next(a),c)\ \mathrm{then}\ b = c \}.$$ We wish to show that $B = \nats$ by induction. For the base case, we need to show that $b = \zero \in B$; for this it suffices to show that $C(\zero) = \nats$, which we do by induction. For the base case $c = \zero$, we have $b = c$ regardless of $a$. For the inductive step suppose we have $c \in C(\zero)$ for some $c$. Note that $$\begin{eqnarray*} & & \ntimes(\next(a),\next(c)) \\ & = & \nplus(\ntimes(a,\next(c)),\next(c)) \\ & = & \next(\nplus(\ntimes(a,\next(c)),c)) \end{eqnarray*}$$ while $$\ntimes(\next(a),b) = \ntimes(\next(a),\zero) = \zero;$$ in particular, the statement $$\ntimes(\next(a),\next(c)) = \ntimes(\next(a),b)$$ is false, so that $\next(c) \in C(\zero)$ *vacuously*. So we have $C(\zero) = \nats$, and thus $\zero \in B$. For the inductive step, suppose we have $b \in B$; we wish to show that $\next(b) \in B$, or equivalently that $C(\next(b)) = \nats$. We proceed by induction on $c$ again. The base case $c = \zero$ holds vacuously. For the inductive step, suppose we have $c \in C(\next(b))$. Now suppose further that $$\ntimes(\next(a),\next(b)) = \ntimes(\next(a),\next(c)).$$ Note that $$\begin{eqnarray*} & & \ntimes(\next(a),\next(b)) \\ & = & \nplus(\ntimes(a,\next(c),\next(c)) \\ & = & \next(\nplus(\ntimes(\next(c),a),c)) \\ & = & \next(\nplus(\nplus(\ntimes(c,a),a),c)) \\ & = & \next(\nplus(\nplus(\ntimes(a,c),c),a)). \end{eqnarray*}$$ The analogous statement holds for $b$. So we have $$\begin{eqnarray*} \next(\nplus(\nplus(\ntimes(a,b),b),a)) & = & \next(\nplus(\nplus(\ntimes(a,c),c),a)) \\ \nplus(\nplus(\ntimes(a,b),b),a) & = & \nplus(\nplus(\ntimes(a,c),c),a) \\ \nplus(\ntimes(a,b),b) & = & \nplus(\ntimes(a,c),c) \\ \ntimes(\next(a),b) & = & \ntimes(\next(a),c) \\ b & = & c \end{eqnarray*}$$ as needed.
10. Follows from (5) and (9).
</p></div>
</div>


Implementation and Testing
--------------------------

As with $\nplus$, it's a good idea to test the properties of $\ntimes$.

> _test_times_zero_left :: (Natural n)
>   => n -> Test (Nat n -> Bool)
> _test_times_zero_left _ =
>   testName "0 == times(0,a)" $
>   \a -> zero ==== times zero a
> 
> 
> _test_times_zero_right :: (Natural n)
>   => n -> Test (Nat n -> Bool)
> _test_times_zero_right _ =
>   testName "0 == times(a,0)" $
>   \a -> zero ==== times a zero
> 
> 
> _test_times_one_left :: (Natural n)
>   => n -> Test (Nat n -> Bool)
> _test_times_one_left _ =
>   testName "a == times(1,a)" $
>   \a -> a ==== times (next zero) a
> 
> 
> _test_times_one_right :: (Natural n)
>   => n -> Test (Nat n -> Bool)
> _test_times_one_right _ =
>   testName "a == times(a,1)" $
>   \a -> a ==== times a (next zero)
> 
> 
> _test_times_next_left :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_times_next_left _ =
>   testName "times(next(a),b) == plus(times(a,b),b)" $
>   \a b -> (times (next a) b) ==== (plus (times a b) b)
> 
> 
> _test_times_next_right :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_times_next_right _ =
>   testName "times(a,next(b)) == plus(times(a,b),a)" $
>   \a b -> (times a (next b)) ==== (plus (times a b) a)
> 
> 
> _test_times_commutative :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_times_commutative _ =
>   testName "times(a,b) == times(b,a)" $
>   \a b -> (times a b) ==== (times b a)
> 
> 
> _test_times_distributive_left :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Nat n -> Bool)
> _test_times_distributive_left _ =
>   testName "times(a,plus(b,c)) == plus(times(a,b),times(a,c))" $
>   \a b c -> (times a (plus b c)) ==== (plus (times a b) (times a c))
> 
> 
> _test_times_distributive_right :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Nat n -> Bool)
> _test_times_distributive_right _ =
>   testName "times(plus(a,b),c) == plus(times(a,c),times(b,c))" $
>   \a b c -> (times (plus a b) c) ==== (plus (times a c) (times b c))
> 
> 
> _test_times_associative :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Nat n -> Bool)
> _test_times_associative _ =
>   testName "times(times(a,b),c) == times(a,times(b,c))" $
>   \a b c -> (times (times a b) c) ==== (times a (times b c))

And one function to rule them all:

> _test_times :: (TypeName n, Natural n, Arbitrary n, Show n)
>   => n -> Int -> Int -> IO ()
> _test_times n maxSize numCases = do
>   testLabel ("times: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_times_zero_left n)
>   runTest args (_test_times_zero_right n)
>   runTest args (_test_times_one_left n)
>   runTest args (_test_times_one_right n)
>   runTest args (_test_times_next_left n)
>   runTest args (_test_times_next_right n)
>   runTest args (_test_times_commutative n)
>   runTest args (_test_times_distributive_left n)
>   runTest args (_test_times_distributive_right n)
>   runTest args (_test_times_associative n)

I used a much smaller number of test cases this time, because these run much more slowly than the tests for ``plus``. The culprit is ``_test_times_associative``. What's happening is that multiplication of ``Nat``s is inherently slow; it's implemented as iterated addition, which itself is iterated ``N``.

The problem lies in our *representation* of the natural numbers. A better representation might make a more efficient ``times`` possible.

> main_times :: IO ()
> main_times = do
>   _test_times (zero :: Unary) 20 100
