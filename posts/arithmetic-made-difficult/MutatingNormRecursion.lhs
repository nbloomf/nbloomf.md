---
title: Mutating Norm Recursion
author: nbloomf
date: 2018-01-19
tags: arithmetic-made-difficult, literate-haskell
slug: mnormrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module MutatingNormRecursion (
>   mnormrec
> ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import Unary
> import NaturalNumbers
> import MutatingRecursion

Just as mutating recursion generalizes bailout recursion at the expense of losing the tail recursive evaluation strategy,  it will be handy to have a generalization of norm recursion that sacrifices tail recursion. We'll call this *mutating norm recursion*.

:::::: theorem :::::
Let $(A,\varepsilon,\varphi)$ be an inductive set, and let $\eta : A \rightarrow \nats$ be an inductive norm. Now suppose we have mappings $\delta : A \rightarrow B$ and $\sigma : A \times B \rightarrow B$. Then there is a unique map $\Theta : A \rightarrow B$ such that.
$$\Theta(a) = \left\{\begin{array}{l}
 \delta(a) & \mathrm{if}\ \iszero(\eta(a)) \\
 \sigma(a,\Theta(\varphi(a))) & \mathrm{otherwise}
\end{array}\right.$$
We denote this unique map by $\mnormrec(\varphi)(\eta)(\delta)(\sigma)$.

::: proof ::::::::::
We define maps $\beta : \nats \times A \rightarrow \bool$ by $$\beta(n,a) = \iszero(\eta(a)),$$ $\psi : \nats \times A \rightarrow B$ by $$\psi(n,a) = \delta(a),$$ $\chi : \nats \times A \times B \rightarrow B$ by $$\chi(n,a,b) = \sigma(a,b),$$ and $\omega : \nats \times A \rightarrow A$ by $$\omega(n,a) = \varphi(a).$$ Now we define $\Omega : \nats \times A \rightarrow B$ by $$\Omega = \mutrec(\delta)(\beta)(\psi)(\chi)(\omega).$$

We first need the following intermediate result: for all $a \in A$ and $k \in \nats$, we claim that $$\Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) = \Omega(\eta(\varphi(a)),\varphi(a)).$$ To see this, we proceed by strong induction on $\eta(\varphi(a))$. For the base case, suppose $\eta(\varphi(a)) = \zero$; we show the equality holds by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) \\
 & = & \Omega(\nplus(\zero,\zero),\varphi(a)) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \Omega(\zero,\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $k$ when $\eta(\varphi(a)) = \zero$. Now
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),\next(k)),\varphi(a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \Omega(\next(\nplus(\eta(\varphi(a)),k)),\varphi(a)) \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a))))} \\
 & = & \bif{\btrue}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a))))} \\
 &     \href{@booleans@#cor-if-true}
   = & \delta(\varphi(a)) \\
 & = & \bif{\btrue}{\delta(\varphi(a))}{} \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(\eta(\varphi(a)),\varphi(\varphi(a))))} \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a))
\end{eqnarray*}$$
as needed.

For the strong inductive step, suppose the equality holds for all $k$ whenever $\nleq(\eta(\varphi(a)),m)$ for some $m$, and suppose further that $\eta(\varphi(a)) = \next(m)$. We proceed by induction on $k$. For the base case $k = \zero$, of course we have
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) \\
 & = & \Omega(\nplus(\eta(\varphi(a)),\zero),\varphi(a)) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & \Omega(\eta(\varphi(a)),\varphi(a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $k$. Now
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),\next(k)),\varphi(a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \Omega(\next(\nplus(\eta(\varphi(a)),k)),\varphi(a)) \\
 & = & \bif{\iszero(\varphi(a))}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a))))} \\
 & = & \sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a)))) \\
 & = & Q.
\end{eqnarray*}$$
Note that $\eta(\varphi(a)) = \next(m)$, so that \nleq(\eta(\varphi(\varphi(a))),m)$, and thus $\nplus(\eta(\varphi(\varphi(a))),u) = m$ for some $u$. Now
$$\begin{eqnarray*}
 &   & \nplus(\eta(\varphi(a)),k) \\
 & = & \nplus(\next(m),k) \\
 & = & \nplus(m,\next(k)) \\
 & = & \nplus(\nplus(\eta(\varphi(\varphi(a))),u),\next(k)) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\eta(\varphi(\varphi(a))),\nplus(u,\next(k)))
\end{eqnarray*}$$
Using the strong induction hypothesis, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(\varphi(a))),\nplus(u,\next(k))),\varphi(\varphi(a)))) \\
 & = & \sigma(\varphi(a),\Omega(\eta(\varphi(\varphi(a))),\varphi(\varphi(a)))) \\
 & = & \sigma(\varphi(a),\Omega(\nplus(\eta(\varphi(\varphi(a))),u),\varphi(\varphi(a)))) \\
 & = & \sigma(\varphi(a),\Omega(m,\varphi(\varphi(a)))) \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(m,\varphi(\varphi(a))))} \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\delta(\varphi(a))}{\sigma(\varphi(a),\Omega(m,\varphi(\varphi(a))))} \\
 & = & \Omega(\next(m),\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a))
\end{eqnarray*}$$
as needed.

Now we define $\Theta : A \rightarrow B$ by $$\Theta(a) = \Omega(\eta(a),a).$$ To see that $\Theta$ has the claimed properties, note that if $\eta(a) = \zero$, we have
$$\begin{eqnarray*}
 &   & \Theta(a) \\
 & = & \Omega(\eta(a),a) \\
 & = & \Omega(\zero,a) \\
 & = & \delta(a).
\end{eqnarray*}$$
If $\eta(a) = \next(m)$, then $\nleq(eta(\varphi(a)),m)$, so that $\nplus(\eta(\varphi(a)),u) = m$ for some $u$. Now
$$\begin{eqnarray*}
 &   & \Theta(a) \\
 & = & \Omega(\eta(a),a) \\
 & = & \Omega(\next(m),a) \\
 & = & \bif{\iszero(\eta(a))}{\delta(a)}{\sigma(a,\Omega(m,\varphi(a)))} \\
 & = & \bif{\iszero(\next(m))}{\delta(a)}{\sigma(a,\Omega(m,\varphi(a)))} \\
 &     \href{@unary@#thm-iszero-next}
   = & \bif{\bfalse}{\delta(a)}{\sigma(a,\Omega(m,\varphi(a)))} \\
 &     \href{@booleans@#cor-if-false}
   = & \sigma(a,\Omega(m,\varphi(a))) \\
 & = & \sigma(a,\Omega(\nplus(\eta(\varphi(a)),u),\varphi(a))) \\
 & = & \sigma(a,\Omega(\eta(\varphi(a)),\varphi(a))) \\
 & = & \sigma(a,\Theta(\varphi(a)))
\end{eqnarray*}$$
as needed.

Finally we show that $\Theta$ is unique. To this end, suppose $\Psi : A \rightarrow B$ is a map such that $\Psi(a) = \delta(a)$ if $\eta(a) = \zero$ and $\Psi(a) = \sigma(a,\Psi(\varphi(a)))$ otherwise. We show that $\Psi(a) = \Theta(a)$ for all $a$ by strong induction on $\eta(a)$. For the base case $\eta(a) = \zero$, we have
$$\begin{eqnarray*}
 &   & \Psi(a) \\
 & = & \delta(a) \\
 & = & \Theta(a)
\end{eqnarray*}$$
as needed. For the inductive step suppose the equality holds for all $a$ such that $\nleq(\eta(a),m)$ for some $m$, and suppose further that $\eta(a) = \next(m)$. Now $\nleq(\eta(\varphi(a)),m)$, so we have
$$\begin{eqnarray*}
 &   & \Psi(a) \\
 & = & \sigma(a,\Psi(\varphi(a))) \\
 & = & \sigma(a,\Theta(\varphi(a))) \\
 & = & \Theta(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

We have a couple of ways to implement $\mnormrec$.

> mnormrec, mnormrec' :: (Natural n)
>   => (a -> a)
>   -> (a -> n)
>   -> (a -> b)
>   -> (a -> b -> b)
>   -> a
>   -> b

There's the universal property:

> mnormrec phi eta delta sigma a =
>   case unnext (eta a) of
>     Left () -> delta a
>     Right _ -> sigma a (mnormrec phi eta delta sigma (phi a))

And there's the definition from the proof.

> mnormrec' phi eta delta sigma a =
>   mutatingRec delta beta psi chi omega (eta a) a
>   where
>     beta _ a = isZero (eta a)
>     psi _ a = delta a
>     chi _ a b = sigma a b
>     omega _ a = phi a

