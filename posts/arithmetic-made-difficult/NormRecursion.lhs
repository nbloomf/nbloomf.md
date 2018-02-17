---
title: Norm Recursion
author: nbloomf
date: 2017-12-25
tags: arithmetic-made-difficult, literate-haskell
slug: normrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module NormRecursion (
>   normRec
> ) where
> 
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion

The essence of recursion is to solve problems by combining solutions to smaller instances of the same problem. The recursion patterns we've identified so far take a specific and limited view of what "smaller instance" means; the instance smaller than $\next(n)$ is just $n$. We can think of this as the recursion embodied in the induction principle, where we prove theorems about all natural numbers by assuming they hold for $n$ and showing they also hold for $\next(n)$.

We've seen an alternative induction principle -- strong induction -- which allows us to prove theorems by assuming they hold for all $k$ with $\nleq(k,n)$ and showing they hold for $\next(n)$. Logically, strong induction is equivalent to "ordinary" induction, and so is redundant. But as we've seen, the stronger induction hypothesis of strong induction can make some proofs more convenient.

Today we'll establish a recursion pattern analogous to strong induction. 

:::::: definition ::
Let $(A,\varepsilon,\varphi)$ be an iterative set. A map $\eta : A \rightarrow \nats$ is called an *iterative norm* if the following hold for all $a \in A$.

1. If $\eta(a) = \zero$, then $\eta(\varphi(a)) = \zero$.
2. If $\eta(a) = \next(n)$, then $\nleq(\eta(\varphi(a)),n)$.
::::::::::::::::::::

Roughly speaking, an iterative norm is a measure of "size" on $A$ with the property that this size is strictly decreasing under the action of $\varphi$.

:::::: theorem :::::
Let $(A,\varepsilon,\varphi)$ be an iterative set, with $\eta : A \rightarrow \nats$ an iterative norm. Let $B$ be a set, with $\chi : A \rightarrow B$. Then there is a unique map $\Theta : A \rightarrow B$ such that, for all $a \in A$, $$\Theta(a) = \bif{\iszero(\eta(a))}{\chi(a)}{\Theta(\varphi(a))}.$$ This $\Theta$ will be denoted $\normrec(\varphi)(\eta)(\chi)$.

::: proof ::::::::::
We define $\beta : \nats \times A \rightarrow \bool$ by $$\beta(k,a) = \iszero(\eta(a)),$$ define $\psi : \nats \times A \rightarrow B$ by $$\psi(k,a) = \chi(a),$$ and define $\omega : \nats \times A \rightarrow A$ by $$\omega(k,a) = \varphi(a),$$ and $\Omega : \nats \times A \rightarrow B$ by $$\Omega = \bailrec(\chi)(\beta)(\psi)(\omega).$$ As a lemma, we need the following intermediate result: for all $a \in A$ and $k \in \nats$, we have $$\Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) = \Omega(\eta(\varphi(a)),\varphi(a)).$$ We proceed by double induction, starting with strong induction on $\eta(\varphi(a))$. For the base case $\eta(\varphi(a)) = \zero$, we proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) \\
 & = & \Omega(\nplus(\zero,\zero),\varphi(a)) \\
 &     \href{@plus@#cor-plus-up-zero}
   = & \Omega(\zero,\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a)).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $k$. Now
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),\next(k)),\varphi(a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \Omega(\next(\nplus(\eta(\varphi(a)),k)),\varphi(a)) \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\chi(\varphi(a))}{\Omega(\nplus(\eta(\varphi(\varphi(a))),k))} \\
 & = & \bif{\btrue}{\chi(\varphi(a))}{\Omega(\nplus(\eta(\varphi(\varphi(a))),k))} \\
 &     \href{@booleans@#cor-if-true}
   = & \chi(\varphi(a)) \\
 & = & \Omega(\zero,\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a)).
\end{eqnarray*}$$
So if $\eta(\varphi(a)) = \zero$, we have $$\Omega(\nplus(\eta(\varphi(a)),k),\varphi(a)) = \Omega(\eta(\varphi(a)),\varphi(a)).$$ For the strong induction step, suppose we have $m \in \nats$ such that the equality holds for all $k \in \nats$ and all $a \in A$ such that $\nleq(\eta(\varphi(a)),m)$. Suppose further that $a \in A$ such that $\eta(\varphi(a)) = \next(m)$. We proceed by induction on $k$. If $k = \zero$, we have $$\Omega(\nplus(\eta(\varphi(a)),\zero),\varphi(a)) = \Omega(\eta(\varphi(a)),\varphi(a)).$$ For the inductive step suppose the equality holds for some $k$. Now
$$\begin{eqnarray*}
 &   & \Omega(\nplus(\eta(\varphi(a)),\next(k)),\varphi(a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \Omega(\next(\nplus(\eta(\varphi(a)),k)),\varphi(a)) \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\chi(\varphi(a))}{\Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a)))} \\
 & = & \Omega(\nplus(\eta(\varphi(a)),k),\varphi(\varphi(a))) \\
 & = & Q.
\end{eqnarray*}$$
Now note that $\eta(\varphi(a)) = \next(m)$, so $\nleq(\eta(\varphi(\varphi(a))),m)$, and thus $\nplus(\eta(\varphi(\varphi(a))),u) = m$ for some $u$. Then
$$\begin{eqnarray*}
 &   & \nplus(\eta(\varphi(a)),k) \\
 & = & \nplus(\next(m),k) \\
 & = & \nplus(m,\next(k)) \\
 & = & \nplus(\nplus(\eta(\varphi(\varphi(a))),u),\next(k)) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(\eta(\varphi(\varphi(a))),\nplus(u,\next(k)))
\end{eqnarray*}$$
and by the strong induction hypothesis, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \Omega(\nplus(\eta(\varphi(\varphi(a))),\nplus(u,\next(k))),\varphi(\varphi(a))) \\
 & = & \Omega(\eta(\varphi(\varphi(a))),\varphi(\varphi(a))) \\
 & = & \Omega(\nplus(\eta(\varphi(\varphi(a))),u),\varphi(\varphi(a))) \\
 & = & \Omega(m,\varphi(\varphi(a))) \\
 & = & \bif{\iszero(\eta(\varphi(a)))}{\chi(\varphi(a))}{\Omega(m,\varphi(\varphi(a)))} \\
 & = & \Omega(\next(m),\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a))
\end{eqnarray*}$$
as needed.

Now we define $\Theta : A \rightarrow B$ by $$\Theta(a) = \Omega(\eta(a),a).$$

To see that $\Theta$ has the claimed properties, we consider two possibilities for $\eta(a)$. If $\eta(a) = \zero$, we have
$$\begin{eqnarray*}
 &   & \Theta(a) \\
 & = & \Omega(\eta(a),a) \\
 & = & \Omega(\zero,a) \\
 & = & \chi(a).
\end{eqnarray*}$$
If $\eta(a) = \next(m)$, we have $\nleq(\eta(\varphi(a)),m)$, so that $\nplus(\eta(\varphi(a)),u) = m$ for some $u$. Then
$$\begin{eqnarray*}
 &   & \Theta(a) \\
 & = & \Omega(\eta(a),a) \\
 & = & \Omega(\next(m),a) \\
 & = & \bif{\iszero(\eta(a))}{\chi(a)}{\Omega(m,\varphi(a))} \\
 & = & \bif{\next(m)}{\chi(a)}{\Omega(m,\varphi(a))} \\
 & = & \Omega(m,\varphi(a)) \\
 & = & \Omega(\nplus(\eta(\varphi(a)),u),\varphi(a)) \\
 & = & \Omega(\eta(\varphi(a)),\varphi(a)) \\
 & = & \Theta(\varphi(a))
\end{eqnarray*}$$
as claimed.

We show that $\Theta$ is unique by strong induction. Suppose $\Pi$ is another function $A \rightarrow B$ such that $\Pi(a) = \chi(a)$ if $\eta(a) = \zero$ and $\Pi(a) = \Pi(\varphi(a))$ otherwise. For the base case, if $\eta(a) = \zero$, we have $$\Pi(a) = \chi(a) = \Theta(a).$$ For the inductive step, suppose $\Pi(a) = \Theta(a)$ whenever $\nleq(\eta(a),m)$ for some $m$, and suppose $\eta(a) = \next(m)$. Then $\nleq(\eta(\varphi(a)),m)$ and $$\Pi(a) = \Pi(\varphi(a)) = \Theta(\varphi(a)) = \Theta(a)$$ as needed.
::::::::::::::::::::
::::::::::::::::::::

Implementation
--------------

We can implement $\normrec$ using the definition from the theorem...

> normRec, normRec'
>   :: (Natural n)
>   => (a -> a)
>   -> (a -> n)
>   -> (a -> b)
>   -> (a -> b)
> 
> normRec' phi eta chi a = bailoutRec chi beta psi omega (eta a) a
>   where
>     beta _ c = isZero (eta c)
>     psi _ c = chi c
>     omega _ c = phi c

Or by pattern matching, using the universal property.

> normRec phi eta chi a = case unnext (eta a) of
>   Left () -> chi a
>   Right _ -> normRec phi eta chi (phi a)

As with our other recursion operators, $\normrec(\varphi)(\eta)(\chi)$ is the unique solution to a system of functional equations. Specifically, we have the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with $\varphi : A \rightarrow A$, $\eta : A \rightarrow \nats$ an iterative norm on $(A,\varepsilon,\varphi)$ for some $\varepsilon$, and $\chi : A \rightarrow B$. Then $\normrec(\varphi)(\eta)(\chi)$ is the unique solution $f : A \rightarrow B$ to the following functional equation for all $a \in A$:
$$f(a) = \bif{\iszero(\eta(a))}{\chi(a)}{f(\varphi(a))}.$$
::::::::::::::::::::
