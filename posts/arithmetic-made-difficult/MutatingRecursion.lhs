---
title: Mutating Recursion
author: nbloomf
date: 2014-05-22
tags: arithmetic-made-difficult, literate-haskell
slug: mutrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module MutatingRecursion
>   ( mutatingRec, _test_mutatingrec, main_mutatingrec
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import DisjointUnions
> import NaturalNumbers

Note that both simple recursion and bailout recursion produce functions with type $$\nats \times A \rightarrow B;$$ we can call that $A$ argument the *parameter*. Now simple and bailout recursion use the parameter in different ways. Simple recursion is only allowed to change $A$ "outside" the recursive call, while bailout recursion can only change $A$ "inside" the recursive call. These restrictions were necessary so that simple and bailout recursion would have tail-recursive implementations. But there are times when we will want a recursive function with signature $\nats \times A \rightarrow B$ that can change its $A$ parameter both inside and outside the recursion.

For this situation we introduce yet another recursion operator on $\nats$, which we'll call *mutating recursion*.

:::::: theorem :::::
Let $A$ and $B$ be sets, and suppose we have mappings $$\varphi : A \rightarrow B,$$ $$\omega : A \rightarrow A,$$ and $$\chi : A \times B^A \rightarrow B.$$ There is a unique map $\Theta : \nats \rightarrow A \rightarrow B$ such that $$\Theta(\zero)(a) = \varphi(a)$$ and $$\Theta(\next(n))(a) = \chi(\omega(a),\Theta(n)).$$ We will call such functions *mutating recursive*, and denote this $\Theta$ by $\mutrec{\varphi}{\omega}{\chi}$.

::: proof ::::::::::
Define $\Omega : B^A \rightarrow B^A$ by $$\Omega(f)(a) = \chi(\omega(a),f).$$ Now $(B^A, \varphi, \Omega)$ is an inductive set; define $\Theta = \natrec{\varphi}{\Omega}$. Then $\Theta$ is unique such that
$$\begin{eqnarray*}
 &   & \Theta(\zero)(a) \\
 & = & \natrec{\varphi}{\Omega}(\zero)(a) \\
 & = & \varphi(a)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Theta(\next(n))(a) \\
 & = & \natrec{\varphi}{\Omega}(\next(n))(a) \\
 & = & \Omega(\natrec{\varphi}{\Omega}(n))(a) \\
 & = & \chi(\omega(a),\natrec{\varphi}{\Omega}(n)) \\
 & = & \chi(\omega(a),\Theta(n))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

As usual we now want to implement $\mutrec{\ast}{\ast}{\ast}$ in software, and there are a couple of ways to go about this. First, the signature.

> mutatingRec, mutatingRec' :: (Natural n)
>   => (a -> b)
>   -> (a -> a)
>   -> (a -> (a -> b) -> b)
>   -> n
>   -> a
>   -> b

There's the naive way:

> mutatingRec phi omega chi =
>   let
>     theta n a = case unnext n of
>       Left () -> phi a
>       Right m -> chi (omega a) (theta m)
> 
>   in theta

And there's the definition from the proof:

> mutatingRec' phi omega chi =
>   let w f a = chi (omega a) f in
>   naturalRec phi w

The naive implementation of mutating recursion is not tail recursive, and I think (without proof) that no truly tail recursive implementation exists (that is sort of the reason for this operator).

While we're at it, we should test that the two are not *not* equivalent.

> _test_mutatingrec_equiv :: (Natural n, Equal b)
>   => n -> a -> b -> Test ((a -> b) -> (a -> a) -> (a -> (a -> b) -> b) -> n -> a -> Bool)
> _test_mutatingrec_equiv _ _ _ =
>   testName "mutatingRec(phi,omega,chi)(n,a) == mutatingRec'(phi,omega,chi)(n,a)" $
>   \phi omega chi n a -> eq
>     (mutatingRec phi omega chi n a)
>     (mutatingRec' phi omega chi n a)


What it does
------------

As with the other recursion operators, the "uniqueness" part of mutating recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with mappings
$$\begin{eqnarray*}
 \varphi & : & A \rightarrow B \\
 \omega & : & A \rightarrow A \\
 \chi & : & A \times B^A \rightarrow B.
\end{eqnarray*}$$
Then $\mutrec{\varphi}{\omega}{\chi}$ is the unique solution $f : \nats \times A \rightarrow B$ to the following system of functional equations for all $k \in \nats$, $a \in A$:
$$\left\{\begin{array}{l}
 f(\zero)(a) = \varphi(a) \\
 f(\next(n))(a) = \chi(\omega(a),f(n))
\end{array}\right.$$
::::::::::::::::::::


Testing
-------

Suite:

> _test_mutatingrec
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , Equal b, Arbitrary a, CoArbitrary a, Arbitrary b, CoArbitrary b
>   , Show a, Show b, TypeName a, TypeName b, CoArbitrary n)
>   => n -> a -> b -> Int -> Int -> IO ()
> _test_mutatingrec n a b maxSize numCases = do
>   testLabel3 "mutatingRec" n a b
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_mutatingrec_equiv n a b)

Main:

> main_mutatingrec :: IO ()
> main_mutatingrec = do
>   _test_mutatingrec (zero :: Unary) (true :: Bool)  (true :: Bool)  5 50
>   _test_mutatingrec (zero :: Unary) (zero :: Unary) (true :: Bool)  5 50
>   _test_mutatingrec (zero :: Unary) (true :: Bool)  (zero :: Unary) 5 50
>   _test_mutatingrec (zero :: Unary) (zero :: Unary) (zero :: Unary) 5 50
