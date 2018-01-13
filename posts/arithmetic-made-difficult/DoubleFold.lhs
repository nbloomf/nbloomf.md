---
title: Double Fold
author: nbloomf
date: 2018-01-02
tags: arithmetic-made-difficult, literate-haskell
slug: dfoldr
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DoubleFold (
>   dfoldr
> ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import Lists

Every $A$-inductive homomorphism $\lists{A} \rightarrow B$ can be defined in terms of $\foldr{\ast}{\ast}$. But, as with $\nats$, some specializations of $\foldr{\ast}{\ast}$ show up often enough to warrant their own name. Today we'll define one of these, analogous to $\dnatrec{\ast}{\ast}{\ast}$.

<div class="result">
<div class="thm">
Let $A$, $B$, and $C$ be sets, and suppose we have mappings $$\begin{array}{l} \delta : \lists{B} \rightarrow C \\ \psi : A \times C \rightarrow C \\ \chi : A \times B \times \lists{B} \times C \times C \rightarrow C. \end{array}$$ There is a unique solution $\Omega : \lists{A} \times \lists{B} \rightarrow C$ to the following system of functional equations for all $a \in A$, $b \in B$, $x \in \lists{A}$, and $y \in \lists{B}$.
$$\left\{\begin{array}{l}
 \Omega(\nil,y) = \delta(y) \\
 \Omega(\cons(a,x),\nil) = \psi(a,\Omega(x,\nil)) \\
 \Omega(\cons(a,x),\cons(b,y)) = \chi(a,b,y,\Omega(x,y),\Omega(x,\cons(b,y)))
\end{array}\right.$$
We denote this $\Omega$ by $\dfoldr{\delta}{\psi}{\chi}$.

In Haskell:

> dfoldr :: (List t)
>   => (t b -> c)
>   -> (a -> c -> c)
>   -> (a -> b -> t b -> c -> c -> c)
>   -> t a -> t b -> c
> dfoldr delta psi chi = foldr delta phi
>   where
>     phi a f w = case uncons w of
>       Left ()     -> psi a (f nil)
>       Right (b,y) -> chi a b y (f y) (f (cons b y))

</div>

<div class="proof"><p>
Define a map $\varphi : A \times C^{\lists{B}} \rightarrow C^{\lists{B}}$ casewise by
$$\left\{\begin{array}{l}
 \varphi(a,g)(\nil) = \psi(a,g(\nil)) \\
 \varphi(a,g)(\cons(b,v)) = \chi(a,b,v,g(v),g(\cons(b,v))).
\end{array}\right.$$
We claim the unique solution $\Omega : \lists{A} \times \lists{B} \rightarrow C$ is given by $$\Omega(x,y) = \foldr{\delta}{\varphi}(x)(y).$$ First we show that $\Omega$ is actually a solution. To this end let $a \in A$, $b \in B$, $x \in \lists{A}$, and $y \in \lists{B}$, and note that
$$\begin{eqnarray*}
 &   & \Omega(\nil,y) \\
 & = & \foldr{\delta}{\varphi}(\nil)(y) \\
 & = & \delta(y),
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Omega(\cons(a,x),\nil) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\nil) \\
 & = & \psi(a,\foldr{\delta}{\varphi}(x)(\nil)) \\
 & = & \psi(a,\Omega(x,\nil)),
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Omega(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\cons(b,y)) \\
 & = & \chi(a,b,y,\foldr{\delta}{\varphi}(x)(y),\foldr{\delta}{\varphi}(x)(\cons(b,y))) \\
 & = & \chi(a,b,y,\Omega(x,y),\Omega(x,\cons(b,y)))
\end{eqnarray*}$$
as needed. To see uniqueness, suppose $f$ is a solution to the system; we claim that $f(x,y) = \foldr{\delta}{\varphi}(x)(y)$ for all $x,y \in \lists{A}$, and show this by list induction on $x$. For the base case $x = \nil$, for all $y \in \lists{B}$ we have
$$\begin{eqnarray*}
 &   & f(\nil,y) \\
 & = & \delta(y) \\
 & = & \foldr{\delta}{\varphi}(\nil)(y)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $w \in \lists{B}$ for some $x \in \lists{A}$, and let $a \in A$. We consider two possibilities for $w$. If $w = \nil$, we have
$$\begin{eqnarray*}
 &   & f(\cons(a,x),\nil) \\
 & = & \psi(a,f(x,\nil)) \\
 & = & \psi(a,\foldr{\delta}{\varphi}(x)(\nil)) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\nil) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\nil)
\end{eqnarray*}$$
as claimed. If $w = \cons(b,y)$, we instead have
$$\begin{eqnarray*}
 &   & f(\cons(a,x),\cons(b,y)) \\
 & = & \chi(a,b,y,f(x,y),f(x,\cons(b,y))) \\
 & = & \chi(a,b,y,\foldr{\delta}{\varphi}(x)(y),\foldr{\delta}{\varphi}(x)(\cons(b,y))) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(\cons(b,y)) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(\cons(b,y)) \\
\end{eqnarray*}$$
as claimed. By induction, we thus have $$f(x,y) = \foldr{\delta}{\varphi}(x)(y) = \Omega(x,y).$$
</p></div>
</div>
