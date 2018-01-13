---
title: Consuming Fold
author: nbloomf
date: 2018-01-08
tags: arithmetic-made-difficult, literate-haskell
slug: cfoldr
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module ConsumingFold (
>   cfoldr, _test_cfoldr, main_cfoldr
> ) where
> 
> import Testing
> import Booleans
> import Unary
> import Lists

Today we'll implement another recursion operator on lists. This one is similar to $\foldr{\ast}{\ast}$ but allows us to "have our cake and eat it too" in a straightforward way.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, with $\gamma \in B$ and $\sigma : A \times \lists{A} \times B \rightarrow B$. Then there is a unique map $\Omega : \lists{A} \rightarrow B$ such that $$\Omega(\nil) = \gamma$$ and $$\Omega(\cons(a,x)) = \sigma(a,x,\Omega(x)).$$ We denote this map by $\cfoldr{\gamma}{\sigma}$.
</p></div>

<div class="proof"><p>
Define $\varphi : A \times B^{\lists{A}} \rightarrow B^{\lists{A}}$ casewise by
$$\varphi(a,g)(x) = \left\{\begin{array}{ll}
 \sigma(a,\nil,g(\nil)) & \mathrm{if}\ x = \nil \\
 \sigma(a,u,g(u)) & \mathrm{if}\ x = \cons(a,u),
\end{array}\right.$$
and define $\Omega(x) = \foldr{\const(\gamma)}{\varphi}(x)(x)$. Note that
$$\begin{eqnarray*}
 &   & \Omega(\nil) \\
 & = & \foldr{\const(\gamma)}{\varphi}(\nil)(\nil) \\
 & = & \const(\gamma)(\nil) \\
 & = & \gamma
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Omega(\cons(a,x)) \\
 & = & \foldr{\const(\gamma)}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\const(\gamma)}{\varphi}(x))(\cons(a,x)) \\
 & = & \sigma(a,x,\foldr{\const(\gamma)}{\varphi}(x)(x)) \\
 & = & \sigma(a,x,\Omega(x))
\end{eqnarray*}$$
as needed. Suppose now that $\Psi$ also has this property; we see that $\Psi = \Omega$ by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \Psi(\nil) \\
 & = & \gamma \\
 & = & \Omega(\nil),
\end{eqnarray*}$$
and for the inductive step, suppose $\Psi(x) = \Omega(x)$; then we have
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,x)) \\
 & = & \sigma(a,x,\Psi(x)) \\
 & = & \sigma(a,x,\Omega(a)) \\
 & = & \Omega(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Implementation
--------------

We have a few strategies for implementing $\cfoldr{\ast}{\ast}$.

> cfoldr, cfoldr'
>   :: (List t)
>   => b -> (a -> t a -> b -> b) -> t a -> b

There's the definition from the theorem:

> cfoldr' gamma sigma x = foldr (const gamma) phi x x
>   where
>     phi a g x = case uncons x of
>       Left () -> sigma a nil (g nil)
>       Right (b,u) -> sigma b u (g u)

And there's the definition using the universal property.

> cfoldr gamma sigma x = case uncons x of
>   Left () -> gamma
>   Right (a,x) -> sigma a x (cfoldr gamma sigma x)

We should test that the two implementations are not *not* equivalent.

> _test_cfoldr_equiv :: (List t, Equal (t a), Equal a)
>   => t a -> Test (a -> (a -> t a -> a -> a) -> t a -> Bool)
> _test_cfoldr_equiv _ =
>   testName "cfoldr(gamma,sigma)(x) == cfoldr'(gamma,sigma)(x)" $
>   \gamma sigma x -> eq (cfoldr gamma sigma x) (cfoldr' gamma sigma x)


Testing
-------

Suite:

> _test_cfoldr ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a), CoArbitrary (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_cfoldr t maxSize numCases = do
>   testLabel1 "cfoldr" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_cfoldr_equiv t)

Main:

> main_cfoldr :: IO ()
> main_cfoldr = do
>   _test_cfoldr (nil :: ConsList Bool)  20 100
>   _test_cfoldr (nil :: ConsList Unary) 20 100
