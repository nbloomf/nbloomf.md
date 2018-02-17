---
title: Left Fold
author: nbloomf
date: 2018-01-04
tags: arithmetic-made-difficult, literate-haskell
slug: foldl
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module LeftFold (
>   foldl, _test_foldl, main_foldl
> ) where
> 
> import Testing
> import Functions
> import Tuples
> import DisjointUnions
> import Unary
> import Lists

Our goal today is to get as close as possible to a tail-recursive implementation of $\foldr(\ast)(\ast)$.

:::::: theorem :::::
[]{#def-foldl-nil}[]{#def-foldl-cons}
Let $A$ and $B$ be sets, with $f : B \times A \rightarrow B$. There is a unique map $\Theta : B \times \lists{A} \rightarrow B$ such that $$\Theta(e,\nil) = e$$ and $$\Theta(e,\cons(a,x)) = \Theta(f(e,a),x).$$ We denote this map by $\foldl(f)$.

::: proof ::::::::::
First we show existence. Define $\psi : A \times \lists{A}^B \rightarrow \lists{A}^B$ by $$\psi(a,g)(b) = g(f(b,a)),$$ and define $\Theta : B \times \lists{A} \rightarrow B$ by $$\Theta(b,x) = \foldr(\id)(\psi)(x)(b).$$ Now
$$\begin{eqnarray*}
 &   & \Theta(e,\nil) \\
 & = & \foldr(\id)(\psi)(\nil)(e) \\
 &     \href{@lists@#def-foldr-nil}
   = & \id(e) \\
 &     \href{@functions@#def-id}
   = & e
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Theta(e,\cons(a,x)) \\
 & = & \foldr(\id)(\psi)(\cons(a,x))(e) \\
 & = & \psi(a,\foldr(\id)(\psi))(x)(e) \\
 & = & \foldr(\id)(\psi)(x)(f(e,a)) \\
 & = & \Theta(f(e,a),x)
\end{eqnarray*}$$
as claimed.

Now we show that $\Theta$ is unique with this property; to that end, suppose we have a map $\Omega : B \times \lists{A} \rightarrow B$ such that $\Omega(e,\nil) = e$ and $\Omega(e,\cons(a,x)) = \Omega(f(e,a),x)$ for all $e \in B$, $a \in A$, and $x \in \lists{A}$. We show that $\Omega(e,x) = \Theta(e,x)$ by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \Omega(e,\nil) \\
 & = & e \\
 & = & \Theta(e,\nil).
\end{eqnarray*}$$
For the inductive step, suppose $\Omega(e,x) = \Theta(e,x)$, for all $e \in B$ and some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \Omega(e,\cons(a,x)) \\
 & = & \Omega(f(e,a),x) \\
 & = & \Theta(f(e,a),x) \\
 & = & \Theta(e,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

We have a few options for implementing $\foldl(\ast)$.

> foldl, foldl' :: (List t) => (b -> a -> b) -> b -> t a -> b

There's the definition from the proof:

> foldl' f e x = foldr id psi x e 
>   where
>     psi a g b = g (f b a)

$\psi : A \times \lists{A}^B \rightarrow \lists{A}^B$ by $$\psi(a,g)(b) = g(f(a,b)),$$ and define $\Theta : B \times \lists{A} \rightarrow B$ by $$\Theta(b,x) = \foldr(\id)(\psi)(x)(b).$$

And there's the definition from the universal property:

> foldl f e z = case uncons z of
>   Left ()          -> e
>   Right (Pair a x) -> foldl f (f e a) x

We should verify that the two implementations are not *not* equivalent.

> _test_foldl_equiv :: (List t, Equal (t a), Equal a)
>   => t a -> Test ((a -> a -> a) -> a -> t a -> Bool)
> _test_foldl_equiv _ =
>   testName "foldl(f,e)(x) == foldl'(f,e)(x)" $
>   \f e x -> eq (foldl f e x) (foldl' f e x)


Testing
-------

Suite:

> _test_foldl ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_foldl t size cases = do
>   testLabel1 "foldl" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_foldl_equiv t)

Main:

> main_foldl :: IO ()
> main_foldl = do
>   _test_foldl (nil :: ConsList Bool)  20 100
>   _test_foldl (nil :: ConsList Unary) 20 100
