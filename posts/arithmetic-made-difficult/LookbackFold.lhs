---
title: Lookback Fold
author: nbloomf
date: 2018-07-17
tags: arithmetic-made-difficult, literate-haskell
slug: lfold
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module LookbackFold (
>   lfoldr
> ) where
> 
> import Testing
> import Functions
> import Tuples
> import DisjointUnions
> import Lists
> import HeadAndTail
> import LeftFold
> import Reverse
> import Zip

Today we'll implement another recursion operator on lists, this one analogous to the recursion for efficiently computing the $n$th Fibonacci number.

:::::: theorem :::::
Let $A$ and $B$ be sets, with $\theta \in B$, $\lambda : A \rightarrow B$, and $\mu : A \times A \times B \times B \rightarrow B$. There is a unique map $\Psi : \lists{A} \rightarrow B$ such that $$\Psi(\nil) = \theta,$$ $$\Psi(\cons(a,\nil)) = \lambda(a),$$ and $$\Psi(\cons(a,\cons(b,x))) = \mu(a,b,\Psi(\cons(b,x)),\Psi(x)).$$ We call this function *lookback fold* and denote it by $\lfoldr(\theta)(\lambda)(\mu)$.

In Haskell:

> lfoldr
>   :: (List t)
>   => b
>   -> (a -> b)
>   -> (a -> a -> b -> b -> b)
>   -> t a -> b
> lfoldr theta lambda mu x =
>   snd (foldl phi (alpha x) (rev (zip x (tail x))))
> 
>   where
>     alpha x = tup theta (either (const theta) lambda (last x))
> 
>     phi h k = tup (snd h) (mu (fst k) (snd k) (snd h) (fst h))

::: proof ::::::::::
First we define $\alpha : \lists{A} \rightarrow B \times B$ by $$\alpha(x) = \tup(\theta)(\either(\const(\theta))(\lambda)(\last(x)))$$ and $\varphi : (B \times B) \times (A \times A) \rightarrow B \times B$ by $$\varphi(\tup(u)(v),\tup(a)(b)) = \tup(v,\mu(a,b,v,u)).$$ Now define $\Omega : \lists{A} \rightarrow B \times B$ by $$\Omega(x) = \foldl(\varphi)(\alpha(x))(\rev(\zip(x,\tail(x)))).$$

Next we need to establish some technical lemmas. The first is that $$\alpha(\cons(a,\cons(b,x))) = \alpha(\cons(b,x))$$ for all $a,b \in A$ and $x \in \lists{A}$. To see this, note that
$$\begin{eqnarray*}
 &   & \alpha(\cons(a,\cons(b,x))) \\
 & = & \tup(\theta)(\either(\const(\theta))(\lambda)(\last(\cons(a,\cons(b,x))))) \\
 & = & \tup(\theta)(\either(\const(\theta))(\lambda)(\last(\cons(b,x)))) \\
 & = & \alpha(\cons(b,x))
\end{eqnarray*}$$
as needed.

Second, we show that for all $a \in A$ and $x \in \lists{A}$, we have $$\fst(\Omega(\cons(a,x))) = \snd(\Omega(x)).$$ We prove this by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \fst(\Omega(\cons(a,x))) \\
 & = & \fst(\Omega(\cons(a,\nil))) \\
 & = & \fst(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\zip(\cons(a,\nil))(\tail(\cons(a,\nil)))))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\zip(\cons(a,\nil))(\nil)))) \\
 &     \href{@zip@#cor-zip-cons-nil}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\nil))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\nil)) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \fst(\alpha(\cons(a,\nil))) \\
 & = & \fst(\tup(\theta)(\either(\const(\theta))(\lambda)(\last(\cons(a,\nil))))) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \theta \\
 &     \href{@tuples@#thm-snd-tup}
   = & \snd(\tup(\theta)(\theta)) \\
 &     \href{@functions@#def-const}
   = & \snd(\tup(\theta)(\const(\theta)(\ast))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\lft(\ast)))) \\
 & = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\last(\nil)))) \\
 & = & \snd(\alpha(\nil)) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \snd(\foldl(\varphi)(\alpha(\nil))(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \snd(\foldl(\varphi)(\alpha(\nil))(\rev(\nil))) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \snd(\foldl(\varphi)(\alpha(\nil))(\rev(\zip(\nil)(\tail(\nil))))) \\
 & = & \snd(\Omega(\nil)) \\
 & = & \snd(\Omega(x))
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $x$. Then we have
$$\begin{eqnarray*}
 &   & \fst(\Omega(\cons(a,\cons(b,x)))) \\
 & = & \fst(\foldl(\varphi)(\alpha(\cons(a,\cons(b,x))))(\rev(\zip(\cons(a,\cons(b,x)))(\tail(\cons(a,\cons(b,x))))))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\cons(b,x))))(\rev(\zip(\cons(a,\cons(b,x)))(\cons(b,x))))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\cons(b,x))))(\rev(\cons(\tup(a)(b),\zip(\cons(b,x))(x))))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \fst(\foldl(\varphi)(\alpha(\cons(a,\cons(b,x))))(\snoc(\tup(a)(b),\rev(\zip(\cons(b,x))(x))))) \\
 & = & \fst(\foldl(\varphi)(\alpha(\cons(b,x)))(\snoc(\tup(a)(b),\rev(\zip(\cons(b,x))(x))))) \\
 &     \href{@snoc@#thm-snoc-foldl}
   = & \fst(\varphi(\foldl(\varphi)(\alpha(\cons(b,x)))(\rev(\zip(\cons(b,x))(x))),\tup(a)(b))) \\
 & = & \fst(\varphi(\Omega(\cons(b,x)),\tup(a)(b))) \\
 & = & \fst(\varphi(\tup(\fst(\Omega(\cons(b,x))))(\snd(\Omega(\cons(b,x)))),\tup(a)(b))) \\
 & = & \fst(\tup(\snd(\Omega(\cons(b,x))))(\mu(a,b,\snd(\Omega(\cons(b,x))),\fst(\Omega(\cons(b,x)))))) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \snd(\Omega(\cons(b,x)))
\end{eqnarray*}$$
as claimed.

Maybe we can see where this is going; $\Omega$ has a (very short) memory, keeping track of two recursive calls so they can be plugged in to $\mu$. We now define $\Psi : \lists{A} \rightarrow B$ by $$\Psi(x) = \snd(\Omega(x)).$$

Note that
$$\begin{eqnarray*}
 &   & \Psi(\nil) \\
 & = & \snd(\Omega(\nil)) \\
 & = & \snd(\foldl(\varphi)(\alpha(\nil))(\rev(\zip(\nil)(\tail(\nil))))) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \snd(\foldl(\varphi)(\alpha(\nil))(\rev(\nil))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \snd(\foldl(\varphi)(\alpha(\nil))(\nil)) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \snd(\alpha(\nil)) \\
 & = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\last(\nil)))) \\
 & = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\lft(\ast)))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \snd(\tup(\theta)(\const(\theta)(\ast))) \\
 &     \href{@functions@#def-const}
   = & \snd(\tup(\theta)(\theta)) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \theta
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,\nil)) \\
 & = & \snd(\Omega(\cons(a,\nil))) \\
 & = & \snd(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\zip(\cons(a,\nil))(\tail(\cons(a,\nil)))))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \snd(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\zip(\cons(a,\nil))(\nil)))) \\
 &     \href{@zip@#cor-zip-cons-nil}
   = & \snd(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\rev(\nil))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \snd(\foldl(\varphi)(\alpha(\cons(a,\nil)))(\nil)) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \snd(\alpha(\cons(a,\nil))) \\
 & = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\last(\cons(a,\nil))))) \\
 & = & \snd(\tup(\theta)(\either(\const(\theta))(\lambda)(\rgt(a)))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \snd(\tup(\theta)(\lambda(a))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \lambda(a)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,\cons(b,x))) \\
 & = & \snd(\Omega(\cons(a,\cons(b,x)))) \\
 & = & \snd(\foldl(\varphi)(\alpha(\cons(a,\cons(b,x))))(\rev(\zip(\cons(a,\cons(b,x)))(\tail(\cons(a,\cons(b,x))))))) \\
 & = & \snd(\foldl(\varphi)(\alpha(\cons(b,x)))(\rev(\zip(\cons(a,\cons(b,x)))(\tail(\cons(a,\cons(b,x))))))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \snd(\foldl(\varphi)(\alpha(\cons(b,x)))(\rev(\zip(\cons(a,\cons(b,x)))(\cons(b,x))))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \snd(\foldl(\varphi)(\alpha(\cons(b,x)))(\rev(\cons(\tup(a)(b),\zip(\cons(b,x))(x))))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \snd(\foldl(\varphi)(\alpha(\cons(b,x)))(\snoc(\tup(a)(b),\rev(\zip(\cons(b,x))(x))))) \\
 &     \href{@snoc@#thm-snoc-foldl}
   = & \snd(\varphi(\foldl(\varphi)(\alpha(\cons(b,x)))(\rev(\zip(\cons(b,x))(x))),\tup(a)(b))) \\
 & = & \snd(\varphi(\Omega(\cons(b,x)),\tup(a)(b))) \\
 & = & \snd(\varphi(\tup(\fst(\Omega(\cons(b,x))))(\snd(\Omega(\cons(b,x)))),\tup(a)(b))) \\
 & = & \snd(\varphi(\tup(\snd(\Omega(x)))(\snd(\Omega(\cons(b,x)))),\tup(a)(b))) \\
 & = & \snd(\tup(\snd(\Omega(\cons(b,x))))(\mu(a,b,\snd(\Omega(\cons(b,x))),\snd(\Omega(x))))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \mu(a,b,\snd(\Omega(\cons(b,x))),\snd(\Omega(x))) \\
 & = & \mu(a,b,\snd(\Omega(\cons(b,x))),\Psi(x)) \\
 & = & \mu(a,b,\Psi(\cons(b,x)),\Psi(x))
\end{eqnarray*}$$
as claimed.

Finally we show that $\Psi$ is unique with this property. To this end, suppose $\Gamma : \lists{A} \rightarrow B$ such that $\Gamma(\nil) = \theta$, $\Gamma(\cons(a,\nil)) = \lambda(a)$, and $\Gamma(\cons(a,\cons(b,x))) = \mu(a,b,\Gamma(\cons(b,x)),\Gamma(x))$ for all $a,b \in A$ and $x \in \lists{A}$. We show that $\Gamma(x) = \Psi(x)$ for all $x$ by strong induction on $\length(x)$.

For the base case $\length(x) = \zero$, we have $x = \nil$. In this case
$$\begin{eqnarray*}
 &   & \Gamma(\nil) \\
 & = & \theta \\
 & = & \Psi(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ with $\nleq(\length(x),n)$ and suppose $\length(x) = \next(n)$. We have two possibilities; if $n = \zero$, then we have $x = \cons(a,\nil)$ for some $a$. Now
$$\begin{eqnarray*}
 &   & \Gamma(\cons(a,\nil)) \\
 & = & \lambda(a) \\
 & = & \Psi(\cons(a,\nil))
\end{eqnarray*}$$
as needed. Suppose instead that $n = \next(m)$; then $x = \cons(a,\cons(b,z))$ for some $a,b \in A$ and $x \in \lists{A}$, where both $z$ and $\cons(b,z)$ satisfy the induction hypothesis. Now
$$\begin{eqnarray*}
 &   & \Gamma(\cons(a,\cons(b,z))) \\
 & = & \mu(a,b,\Gamma(\cons(b,z)),\Gamma(z)) \\
 & = & \mu(a,b,\Psi(\cons(b,z)),\Psi(z)) \\
 & = & \Psi(\cons(a,\cons(b,z)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

As usual, $\lfoldr(\theta)(\lambda)(\mu)$ is the unique solution to a system of equations.

:::::: corollary :::
Let $A$ and $B$ be sets, with $\theta \in B$, $\lambda : A \rightarrow B$, and $\mu : A \times A \times B \times B \rightarrow B$. Then $\lfoldr(\theta)(\lambda)(\mu)$ is the unique solution $f : \lists{A} \rightarrow B$ to the following system of functional equations for all $a,b \in A$ and $x \in \lists{A}$:
$$\left\{\begin{array}{l}
 f(\nil) = \theta \\
 f(\cons(a,\nil)) = \lambda(a) \\
 f(\cons(a,\cons(b,x))) = \mu(a,b,f(\cons(b,x)),f(x))
\end{array}\right.$$
::::::::::::::::::::
