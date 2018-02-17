---
title: Double Natural Recursion
author: nbloomf
date: 2018-01-01
tags: arithmetic-made-difficult, literate-haskell
slug: dnaturalrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DoubleNaturalRecursion (
>   dnaturalRec, _test_dnaturalRec, main_dnaturalRec
> ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import NaturalNumbers

Today we'll implement a slight generalization of natural recursion that allows recursion on two arguments.

:::::: theorem :::::
[]{@#thm-dnatrec-zero-nat}[]{#thm-dnatrec-next-zero}[]{#thm-dnatrec-next-next}
Let $A$ be a set. Let $\delta : \nats \rightarrow A$, $\psi : A \rightarrow A$, and $\chi : \nats \times A \times A \rightarrow A$. Then there is a unique map $Θ : \nats \times \nats \rightarrow A$ such that $$Θ(\zero,k) = \delta(k),$$ $$Θ(\next(n),\zero) = \psi(Θ(n,\zero)),$$ and $$Θ(\next(n),\next(k)) = \chi(k,Θ(n,k),Θ(n,\next(k))).$$ We denote this map by $\dnatrec{\delta}{\psi}{\chi}.$$

::: proof ::::::::::
Define $φ : A^\nats \rightarrow A^\nats$ casewise by
$$\begin{eqnarray*}
 φ(g)(\zero) & = & \psi(g(\zero)) \\
 φ(g)(\next(k)) & = & \chi(k,g(k),g(\next(k))).
\end{eqnarray*}$$
We then define $Θ : \nats \times \nats \rightarrow A$ by $$Θ(n,k) = \natrec(\delta)(φ)(n)(k).$$

First we show that $Θ$ satisfies the claimed equations. To this end, note that
$$\begin{eqnarray*}
 &   & Θ(\zero,k) \\
 &     \let{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \natrec(\delta)(φ)(\zero)(k) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \delta(k)
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & Θ(\next(n),\zero) \\
 &     \let{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \natrec(\delta)(φ)(\next(n))(\zero) \\
 &     \href{@peano@#cor-natrec-next}
   = & φ(\natrec(\delta)(φ)(n))(\zero) \\
 &     \hyp{φ(g)(\zero) = \psi(g(\zero))}
   = & \psi(\natrec(\delta)(φ)(n)(\zero)) \\
 &     \let{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \psi(Θ(n,\zero))
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & Θ(\next(n),\next(k)) \\
 &     \let{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \natrec(\delta)(φ)(\next(n))(\next(k)) \\
 &     \href{@peano@#cor-natrec-next}
   = & φ(\natrec(\delta)(φ)(n))(\next(k)) \\
 &     \hyp{φ(g)(\next(k)) = \chi(k,g(k),g(\next(k)))}
   = & \chi(k,\natrec(\delta)(φ)(n)(k),\natrec(\delta)(φ)(n)(\next(k))) \\
 &     \hyp{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \chi(k,Θ(n,k),\natrec(\delta)(φ)(n)(\next(k))) \\
 &     \hyp{Θ(n,k) = \natrec(\delta)(φ)(n)(k)}
   = & \chi(k,Θ(n,k),Θ(n,\next(k)))
\end{eqnarray*}$$
as claimed.

Next suppose $\Psi : \nats \times \nats \rightarrow A$ also satisfies these equations. We show that $\Psi = Θ$ by induction on $n$. For the base case $n = \zero$ for all $k$ we have
$$\begin{eqnarray*}
 &   & \Psi(\zero,k) \\
 &     \hyp{\Psi(\zero,k) = \delta(k)}
   = & \delta(k) \\
 &     \hyp{Θ(\zero,k) = \delta(k)}
   = & Θ(\zero,k)
\end{eqnarray*}$$
as needed. For the inductive step, suppose $\Psi(n,k) = Θ(n,k)$ for all $k$ for some $n$. Now let $k \in \nats$. We have two possibilities; if $k = \zero$, then
$$\begin{eqnarray*}
 &   & \Psi(\next(n),\zero) \\
 &     \hyp{\Psi(\next(n),\zero) = \psi(\Psi(n,\zero))}
   = & \psi(\Psi(n,\zero)) \\
 &     \hyp{Θ(n,\zero) = \Psi(n,\zero)}
   = & \psi(Θ(n,\zero)) \\
 &     \hyp{Θ(\next(n),\zero) = \psi(Θ(n,\zero))}
   = & Θ(\next(n),\zero)
\end{eqnarray*}$$
and if $k = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \Psi(\next(n),\next(m)) \\
 &     \hyp{\Psi(\next(n),\next(m)) = \chi(\next(m),\Psi(n,m),\Psi(n,\next(m)))}
   = & \chi(\next(m),\Psi(n,m),\Psi(n,\next(m))) \\
 &     \let{Θ(n,m) = \Psi(n,m)}
   = & \chi(\next(m),Θ(n,m),Θ(n,\next(m))) \\
 &     \hyp{Θ(\next(n),\next(m)) = \chi(\next(m),Θ(n,m),Θ(n,\next(m)))}
   = & Θ(\next(n),\next(m))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

There's a couple of ways to implement $\dnatrec{\ast}{\ast}{\ast}$.

> dnaturalRec, dnaturalRec' :: (Natural n)
>   => (n -> a)
>   -> (a -> a)
>   -> (n -> a -> a -> a)
>   -> n -> n -> a

We can use the definition in the theorem:

> dnaturalRec' delta psi chi = naturalRec delta phi
>   where
>     phi g k = case unnext k of
>       Left () -> psi (g zero)
>       Right m -> chi m (g m) (g (next m))

And there's the definition from the universal property:

> dnaturalRec delta psi chi n k = case unnext n of
>   Left () -> delta k
>   Right m -> case unnext k of
>     Left () -> psi (dnaturalRec delta psi chi m zero)
>     Right t -> chi t
>       (dnaturalRec delta psi chi m t)
>       (dnaturalRec delta psi chi m (next t))

While we're here, we should test that these two implementations aren't not equivalent.

> _test_dnaturalRec_equiv
>   :: (Natural n, Equal a)
>   => n -> a
>   -> Test ((n -> a) -> (a -> a) -> (n -> a -> a -> a) -> n -> n -> Bool)
> _test_dnaturalRec_equiv _ _ =
>   testName "dnaturalRec == dnaturalRec'" $
>   \delta psi chi n k -> eq
>     (dnaturalRec delta psi chi n k)
>     (dnaturalRec' delta psi chi n k)

The "uniqueness" part of double natural recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ be a set, with $\delta : \nats \rightarrow A$, and $\psi : A \rightarrow A$, and $\chi : \nats \times A \times A \rightarrow A$. Then $\dnatrec{\delta}{\psi}{\chi}$ is the unique solution $f : \nats \times \nats \rightarrow A$ to the following system of functional equations for all $n,k \in \nats$:
$$\left\{\begin{array}{l}
 f(\zero,k) = \delta(k) \\
 f(\next(n),\zero) = \psi(f(n,\zero)) \\
 f(\next(n),\next(k)) = \chi(k,f(n,k),f(n,\next(k)))
\end{array}\right.$$
::::::::::::::::::::


Testing
-------

Suite:

> _test_dnaturalRec ::
>   ( TypeName n, Show n, Equal n, Arbitrary n, CoArbitrary n, Natural n
>   , CoArbitrary a, Arbitrary a, Show a, Equal a, TypeName a
>   ) => n -> a -> Int -> Int -> IO ()
> _test_dnaturalRec n a size cases = do
>   testLabel2 "dnaturalRec" n a
> 
>   let
>     args = stdArgs
>       { maxSuccess = cases
>       , maxSize    = size
>       }
> 
>   runTest args (_test_dnaturalRec_equiv n a)

Main:

> main_dnaturalRec :: IO ()
> main_dnaturalRec = do
>   _test_dnaturalRec (zero :: Unary) (zero :: Unary) 10 50
>   _test_dnaturalRec (zero :: Unary) (zero :: Unary) 10 50
>   _test_dnaturalRec (zero :: Unary) (true :: Bool)  10 50
>   _test_dnaturalRec (zero :: Unary) (true :: Bool)  10 50
