---
title: Bailout Fold
author: nbloomf
date: 2018-01-09
tags: arithmetic-made-difficult, literate-haskell
slug: bfoldr
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module BailoutFold (
>   bfoldr, _test_bfoldr, main_bfoldr
> ) where
> 
> import Testing
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers
> import Lists
> import HeadAndTail

In this post we'll develop a list-flavored version of bailout recursion.

:::::: theorem :::::
Let $A$, $B$, and $C$ be sets. Suppose we have mappings $$\delta : B \rightarrow C,$$ $$\beta : A \times \lists{A} \rightarrow B \rightarrow \bool,$$ $$\psi : A \times \lists{A} \times B \rightarrow C,$$ and $$\omega : A \times \lists{A} \times B \rightarrow B.$$ Then there is a unique mapping $\Theta : \lists{A} \times B \rightarrow C$ such that $$\Theta(\nil,u) = \delta(u)$$ and $$\Theta(\cons(a,x),u) = \bif{\beta(a,x,u)}{\psi(a,x,u)}{\Theta(x,\omega(a,x,u))}.$$ We denote this $\Theta$ by $\bfoldr(\delta)(\beta)(\psi)(\omega)$.

::: proof ::::::::::
Define $\varepsilon : B \times \lists{A} \rightarrow C$ by $$\varepsilon(u,x) = \delta(u)$$ and $\varphi : A \times C^{B \times \lists{A}} \rightarrow C^{B \times \lists{A}}$ by $$\varphi(a,g)(u,x) = \bif{\beta(a,\tail(x),u)}{\psi(a,\tail(x),u)}{g(\omega(a,\tail(x),u),\tail(x))},$$ and let $\Theta : \lists{A} \times B \rightarrow C$ be given by $$\Theta(x,u) = \foldr(\varepsilon)(\varphi)(x)(u,x).$$ Note that
$$\begin{eqnarray*}
 &   & \Theta(\nil,u) \\
 & = & \foldr(\varepsilon)(\varphi)(\nil)(u,\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & \varepsilon(u,\nil) \\
 & = & \delta(u)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Theta(\cons(a,x),u) \\
 & = & \foldr(\varepsilon)(\varphi)(\cons(a,x))(u,\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \varphi(a,\foldr(\varepsilon)(\varphi)(x))(u,\cons(a,x)) \\
 & = & \bif{\beta(a,\tail(\cons(a,x)),u)}{\psi(a,\tail(\cons(a,x)),u)}{\foldr(\varepsilon)(\varphi)(x)(\omega(a,\tail(\cons(a,x)),u),\tail(\cons(a,x)))} \\
 & = & \bif{\beta(a,x,u)}{\psi(a,x,u)}{\foldr(\varepsilon)(\varphi)(x)(\omega(a,x,u),x)} \\
 & = & \bif{\beta(a,x,u)}{\psi(a,x,u)}{\Theta(x,\omega(a,x,u))}
\end{eqnarray*}$$
as needed. Suppose $\Psi : \lists{A} \times B \rightarrow C$ also satisfies these equations; we show that $\Psi = \Theta$ by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \Psi(\nil,u) \\
 & = & \delta(u) \\
 & = & \Theta(\nil,u)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $u$ for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,x),u) \\
 & = & \bif{\beta(a,x,u)}{\psi(a,x,u)}{\Psi(x,\omega(a,x,u))} \\
 & = & \bif{\beta(a,x,u)}{\psi(a,x,u)}{\Theta(x,\omega(a,x,u))} \\
 & = & \Theta(\cons(a,x),u)
\end{eqnarray*}$$
so that $\Psi = \Theta$.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

We can implement $\bfoldr$ using the definition or the universal property.

> bfoldr, bfoldr'
>   :: (List t)
>   => (b -> c)
>   -> (a -> t a -> b -> Bool)
>   -> (a -> t a -> b -> c)
>   -> (a -> t a -> b -> b)
>   -> t a -> b -> c
> 
> 
> bfoldr' delta beta psi omega x u = foldr epsilon phi x (tup u x)
>   where
>     epsilon (Pair b _) = delta b
>     phi a g (Pair b y) = if beta a (tail y) b
>       then psi a (tail y) b
>       else g (tup (omega a (tail y) b) (tail y))
> 
> 
> bfoldr delta beta psi omega z u = case uncons z of
>   Left () -> delta u
>   Right (Pair a x) -> if beta a x u
>     then psi a x u
>     else bfoldr delta beta psi omega x (omega a x u)

We should check that these are equivalent.

> _test_bfoldr_equiv :: (List t, Equal (t a), Equal a, Equal c)
>   => t a -> b -> c
>   -> Test ((b -> c) -> (a -> t a -> b -> Bool) -> (a -> t a -> b -> c) -> (a -> t a -> b -> b) -> t a -> b -> Bool)
> _test_bfoldr_equiv _ _ _ =
>   testName "bfoldr(delta,beta,psi,omega)(x,u) == bfoldr'(delta,beta,psi,omega)(x,u)" $
>   \delta beta psi omega x u -> eq
>     (bfoldr delta beta psi omega x u)
>     (bfoldr' delta beta psi omega x u)


Testing
-------

Suite:

> _test_bfoldr ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a), CoArbitrary (t a)
>   , CoArbitrary b, CoArbitrary c, Arbitrary b, Arbitrary c, Show b, Equal c
>   , TypeName b, TypeName c
>   ) => t a -> b -> c -> Int -> Int -> IO ()
> _test_bfoldr t b c size cases = do
>   testLabel3 "bfoldr" t b c
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_bfoldr_equiv t b c)

Main:

> main_bfoldr :: IO ()
> main_bfoldr = do
>   _test_bfoldr (nil :: ConsList Bool)  (zero :: Unary) (zero :: Unary) 50 1000
>   _test_bfoldr (nil :: ConsList Unary) (zero :: Unary) (zero :: Unary) 50 1000
>   _test_bfoldr (nil :: ConsList Bool)  (true :: Bool)  (zero :: Unary) 50 1000
>   _test_bfoldr (nil :: ConsList Unary) (true :: Bool)  (zero :: Unary) 50 1000
