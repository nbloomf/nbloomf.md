---
title: Double Natural Recursion
author: nbloomf
date: 2018-01-01
tags: arithmetic-made-difficult, literate-haskell
slug: dnaturalrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DoubleNaturalRecursion (
>   dnaturalRec
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers

Today we'll implement a slight generalization of natural recursion that allows recursion on two arguments.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Let $\delta : \nats \rightarrow A$, $\psi : A \rightarrow A$, and $\chi : \nats \times A \times A \rightarrow A$. Then there is a unique map $\Theta : \nats \times \nats \rightarrow A$ such that $$\Theta(\zero,k) = \delta(k),$$ $$\Theta(\next(n),\zero) = \psi(\Theta(n,\zero)),$$ and $$\Theta(\next(n),\next(k)) = \chi(k,\Theta(n,k),\Theta(n,\next(k)).$$ We denote this map by $\dnatrec{\delta}{\psi}{\chi}.$$
</p></div>

<div class="proof"><p>
Define $\varphi : A^\nats \rightarrow A^\nats$ casewise by
$$\begin{eqnarray*}
 \varphi(g)(\zero) & = & \psi(g(\zero)) \\
 \varphi(g)(\next(k)) & = & \chi(k,g(k),g(\next(k))).
\end{eqnarray*}$$
We then define $\Theta : \nats \times \nats \rightarrow A$ by $$\Theta(n,k) = \natrec{\delta}{\varphi}(n)(k).$$

First we show that $\Theta$ satisfies the claimed equations. To this end, note that
$$\begin{eqnarray*}
 &   & \Theta(\zero,k) \\
 & = & \natrec{\delta}{\varphi}(\zero)(k) \\
 & = & \delta(k),
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \Theta(\next(n),\zero) \\
 & = & \natrec{\delta}{\varphi}(\next(n))(\zero) \\
 & = & \varphi(\natrec{\delta}{\varphi}(n))(\zero) \\
 & = & \psi(\natrec{\delta}{\varphi}(n)(\zero)) \\
 & = & \psi(\Theta(n,\zero)),
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & \Theta(\next(n),\next(k)) \\
 & = & \natrec{\delta}{\varphi}(\next(n))(\next(k)) \\
 & = & \varphi(\natrec{\delta}{\varphi}(n))(\next(k)) \\
 & = & \chi(k,\natrec{\delta}{\varphi}(n)(k),\natrec{\delta}{\varphi}(n)(\next(k))) \\
 & = & \chi(k,\Theta(n,k),\Theta(n,\next(k)))
\end{eqnarray*}$$
as claimed.

Next suppose $\Psi : \nats \times \nats \rightarrow A$ also satisfies these equations. We show that $\Psi = \Theta$ by induction on $n$. For the base case $n = \zero$ for all $k$ we have
$$\begin{eqnarray*}
 &   & \Psi(\zero,k) \\
 & = & \delta(k) \\
 & = & \Theta(\zero,k)
\end{eqnarray*}$$
as needed. For the inductive step, suppose $\Psi(n,k) = \Theta(n,k)$ for all $k$ for some $n$. Now let $k \in \nats$. We have two possibilities; if $k = \zero$, then
$$\begin{eqnarray*}
 &   & \Psi(\next(n),\zero) \\
 & = & \psi(\Psi(n,\zero)) \\
 & = & \psi(\Theta(n,\zero)) \\
 & = & \Theta(\next(n),\zero),
\end{eqnarray*}$$
and if $k = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \Psi(\next(n),\next(m)) \\
 & = & \chi(k,\Psi(n,m),\Psi(n,\next(m))) \\
 & = & \chi(k,\Theta(n,m),\Theta(n,\next(m))) \\
 & = & \Theta(\next(n),\next(m))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


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

The "uniqueness" part of double natural recursion is also handy. To be a little more explicit, it says the following.

<div class="result">
<div class="thm">
Let $A$ be a set, with $\delta : \nats \rightarrow A$, and $\psi : A \rightarrow A$, and $\chi : \nats \times A \times A \rightarrow A$. Then $\dnatrec{\delta}{\psi}{\chi}$ is the unique solution $f : \nats \times \nats \rightarrow A$ to the following system of functional equations for all $n,k \in \nats$:
$$\left\{\begin{array}{l}
 f(\zero,k) = \delta(k) \\
 f(\next(n),\zero) = \psi(f(n,\zero)) \\
 f(\next(n),\next(k)) = \chi(k,f(n,k),f(n,\next(k)))
\end{array}\right.$$
</div>
</div>
