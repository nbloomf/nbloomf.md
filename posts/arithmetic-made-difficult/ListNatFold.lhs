---
title: List-Natural Fold
author: nbloomf
date: 2018-01-10
tags: arithmetic-made-difficult, literate-haskell
slug: lnfoldr
---

> module ListNatFold (
>   lnfoldr, _test_lnfoldr, main_lnfoldr
> ) where
> 
> import Prelude ()
> import Booleans
> import NaturalNumbers
> import Lists

So far we've developed double recursion on natural numbers and double recursion on lists; today we'll develop a hybrid operator that performs recursion on a list and a natural number simultaneously.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Suppose we have maps $$\delta : \nats \rightarrow B,$$ $$\psi : A \times B \rightarrow B,$$ and $$\chi : A \times \nats \times B \times B \rightarrow B.$$ Then there is a unique map $\Theta : \lists{A} \times \nats \rightarrow B$ such that $$\Theta(\nil,n) = \delta(n),$$ $$\Theta(\cons(a,x),\zero) = \psi(a,\Theta(x,\nil)),$$ and $$\Theta(\cons(a,x),\next(n)) = \chi(a,n,\Theta(x,n),\Theta(x,\next(n)).$$ We denote this $\Theta$ by $\lnfoldr{\delta}{\psi}{\chi}$.
</p></div>

<div class="proof"><p>
Define $\varphi : A \times B^{\lists{A}} \rightarrow B^{\lists{A}}$ casewise by
$$\varphi(a,g)(n) = \left\{\begin{array}{ll}
 \psi(a,g(\zero)) & \mathrm{if}\ n = \zero \\
 \chi(a,n,g(m),g(\next(m))) & \mathrm{if}\ n = \next(m),
\end{array}\right.$$
and let $\Theta(x,n) = \foldr{\delta}{\varphi}(x)(n)$. To see that $\Theta$ solves the given equations, note that
$$\begin{eqnarray*}
 &   & \Theta(\nil,n) \\
 & = & \foldr{\delta}{\varphi}(\nil)(n) \\
 & = & \delta(n),
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \Theta(\cons(a,x),\zero) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\zero) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\zero) \\
 & = & \psi(a,\foldr{\delta}{\varphi}(x)(\zero)) \\
 & = & \psi(a,\Theta(x,\zero)),
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & \Theta(\cons(a,x),\next(n)) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\next(n)) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\next(n)) \\
 & = & \chi(a,n,\foldr{\delta}{\varphi}(x)(n),\foldr{\delta}{\varphi}(x)(\next(n))) \\
 & = & \chi(a,n,\Theta(x,n),\Theta(x,\next(n)))
\end{eqnarray*}$$
as needed. Now suppose $\Psi : \lists{A} \times \nats \rightarrow B$ also satisfies the equations; we show that $\Psi = \Theta$ by list induction. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \Psi(\nil,n) \\
 & = & \delta(n) \\
 & = & \Theta(\nil,n)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equations hold for all $n$ for some $x$, and let $a \in A$. If $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,x),\zero) \\
 & = & \psi(a,\Psi(x,\zero)) \\
 & = & \psi(a,\Theta(x,\zero)) \\
 & = & \Theta(\cons(a,x),\zero),
\end{eqnarray*}$$
and if $n = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,x),\next(m)) \\
 & = & \chi(a,m,\Psi(x,m),\Psi(x,\next(m)) \\
 & = & \chi(a,m,\Theta(x,m),\Theta(x,\next(m)) \\
 & = & \Theta(\cons(a,x),\next(m))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Implementation
--------------

We can implement $\lnfoldr{\ast}{\ast}{\ast}$ using the definition or the universal property.

> lnfoldr, lnfoldr'
>   :: (List t, Natural n)
>   => (n -> b)
>   -> (a -> b -> b)
>   -> (a -> n -> b -> b -> b)
>   -> t a -> n -> b
> 
> 
> lnfoldr' delta psi chi = foldr delta phi
>   where
>     phi a g n = case unnext n of
>       Left () -> psi a (g zero)
>       Right m -> chi a m (g m) (g (next m))
> 
> 
> lnfoldr delta psi chi z k = case uncons z of
>   Left () -> delta k
>   Right (a,x) -> case unnext k of
>     Left () -> psi a (lnfoldr delta psi chi x zero)
>     Right m -> chi a m (lnfoldr delta psi chi x m) (lnfoldr delta psi chi x (next m))

We should check that these two agree.

> _test_lnfoldr_equiv :: (List t, Equal (t a), Equal b, Natural n)
>   => t a -> n -> b
>   -> Test ((n -> b) -> (a -> b -> b) -> (a -> n -> b -> b -> b) -> t a -> n -> Bool)
> _test_lnfoldr_equiv _ _ _ =
>   testName "lnfoldr(delta,psi,chi)(x,n) == lnfoldr'(delta,psi,chi)(x,n)" $
>   \delta psi chi x n -> eq
>     (lnfoldr delta psi chi x n)
>     (lnfoldr' delta psi chi x n)


Testing
-------

Suite:

> _test_lnfoldr ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a), CoArbitrary (t a)
>   , CoArbitrary b, Arbitrary b, Arbitrary n, Show b, Equal n
>   , TypeName b, TypeName n, Equal b, Natural n, CoArbitrary n, Show n
>   ) => t a -> n -> b -> Int -> Int -> IO ()
> _test_lnfoldr t n b maxSize numCases = do
>   testLabel3 "lnfoldr" t n b
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_lnfoldr_equiv t n b)

Main:

> main_lnfoldr :: IO ()
> main_lnfoldr = do
>   _test_lnfoldr (nil :: ConsList Bool)  (zero :: Unary) (zero :: Unary) 20 200
>   _test_lnfoldr (nil :: ConsList Unary) (zero :: Unary) (zero :: Unary) 20 200
>   _test_lnfoldr (nil :: ConsList Bool)  (zero :: Unary) (True)          20 200
>   _test_lnfoldr (nil :: ConsList Unary) (zero :: Unary) (True)          20 200
