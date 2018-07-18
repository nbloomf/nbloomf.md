---
title: Snoc
author: nbloomf
date: 2018-01-05
tags: arithmetic-made-difficult, literate-haskell
slug: snoc
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Snoc (
>   snoc, _test_snoc, main_snoc
> ) where
> 
> import Testing
> import Booleans
> import And
> import Unary
> import Lists
> import HeadAndTail
> import LeftFold

We've defined a set $\lists{A}$ with a special element $\nil$, a map $\cons : A \times \lists{A} \rightarrow \lists{A}$, and a universal map $\foldr(\ast)(\ast)$. As you might guess we'll be thinking of the elements of $\lists{A}$ as finite lists, and they will form a simple kind of data structure.

The $\cons$ function attaches a new item to the "beginning" of a list; we want an analogous function that attaches items to the "end".

First let's tackle adding items to the end of a list; traditionally this operator is called $\snoc$ as a bad pun on "reverse $\cons$". Now the signature of $\snoc$ should be something like $$\snoc : A \times \lists{A} \rightarrow \lists{A},$$ and $\foldr(e)(\varphi)$ can be used to build a map $\lists{A} \rightarrow \lists{A}$, provided $e$ is in $\lists{A}$ and $\varphi : A \times \lists{A} \rightarrow \lists{A}$. Considering the behavior we want $\snoc$ to have, we define the following.

:::::: definition ::
[]{#def-snoc}
Let $A$ be a set. We now define a map $\snoc : A \times \lists{A} \rightarrow \lists{A}$ by $$\snoc(a,x) = \foldr(\cons(a,\nil))(\cons)(x).$$

In Haskell:

> snoc :: (List t) => a -> t a -> t a
> snoc a = foldr (cons a nil) cons

::::::::::::::::::::

Because $\snoc$ is defined directly as a fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-snoc-nil}[]{#cor-snoc-cons}
Let $A$ be a set. Then $\snoc$ is the unique function $f : A \times \lists{A} \rightarrow \lists{A}$ with the property that for all $a,b \in A$ and $x \in \lists{A}$ we have
$$\left\{ \begin{array}{ll}
 f(a,\nil) = \cons(a,\nil) \\
 f(a,\cons(b,x)) = \cons(b,f(a,x)).
\end{array} \right.$$

::: test :::::::::::

> _test_snoc_nil :: (List t, Equal (t a))
>   => t a -> Test (a -> Bool)
> _test_snoc_nil z =
>   testName "snoc(a,nil) == cons(a,nil)" $
>   \a ->
>     let nil' = nil `withTypeOf` z in
>     eq (snoc a nil') (cons a nil')
> 
> 
> _test_snoc_cons :: (List t, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_snoc_cons _ =
>   testName "snoc(a,cons(b,x)) == cons(b,snoc(a,x))" $
>   \a b x -> eq (snoc a (cons b x)) (cons b (snoc a x))

::::::::::::::::::::
::::::::::::::::::::

Now $\snoc$ interacts with $\foldr(\ast)(\ast)$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $e \in B$ and $\varphi : A \times B \rightarrow B$. Then for all $a \in A$ and $x \in \lists{A}$ we have $$\foldr(e)(\varphi)(\snoc(a,x)) = \foldr(\varphi(a,e))(\varphi)(x).$$

::: proof ::::::::::
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldr(e)(\varphi)(\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \foldr(e)(\varphi)(\cons(a,\nil)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \varphi(a,\foldr(e)(\varphi)(\nil)) \\
 &     \href{@lists@#def-foldr-nil}
   = & \varphi(a,e) \\
 &     \href{@lists@#def-foldr-nil}
   = & \foldr(\varphi(a,e))(\varphi)(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \foldr(e)(\varphi)(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \foldr(e)(\varphi)(\cons(b,\snoc(a,x))) \\
 &     \href{@lists@#def-foldr-cons}
   = & \varphi(b,\foldr(e)(\varphi)(\snoc(a,x))) \\
 &     \hyp{\foldr(e)(\varphi)(\snoc(a,x)) = \foldr(\varphi(a,e))(\varphi)(x)}
   = & \varphi(b,\foldr(\varphi(a,e))(\varphi)(x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \foldr(\varphi(a,e))(\varphi)(\cons(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

We can perform case analysis on lists with $\snoc$.

:::::: theorem :::::
Let $A$ be a set and let $x \in \lists{A}$. Then either $x = \nil$ or $x = \snoc(a,w)$ for some $w \in \lists{A}$ and $a \in A$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, the conclusion holds trivially. For the inductive step, suppose the conclusion holds for some $x$ and let $a \in A$. Now $\cons(a,x) \neq \nil$. We have two cases for $x$; if $x = \nil$, then $$\cons(a,x) = \cons(a,\nil) = \snoc(a,\nil)$$ as needed. Suppose instead that $x \neq \nil$; by the inductive hypothesis we have $x = \snoc(b,w)$ for some $b \in A$ and $w \in \lists{A}$. Then we have
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 &     \hyp{x = \snoc(b,w)}
   = & \cons(a,\snoc(b,w)) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(b,\cons(a,w))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::

Also, $\snoc$ interacts with $\beq$.

:::::: theorem :::::
[]{#thm-snoc-eq}
Let $A$ be a set with $a,b \in A$ and $x,y \in \lists{A}$. Then $$\beq(\snoc(a,x),\snoc(b,y)) = \band(\beq(a,b),\beq(x,y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case, set $x = \nil$. We consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(\snoc(a,\nil),\snoc(b,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \beq(\cons(a,\nil),\snoc(b,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \beq(\cons(a,\nil),\cons(b,\nil)) \\
 &     \href{@lists@#thm-list-eq-cons}
   = & \band(\beq(a,b),\beq(\nil,\nil))
\end{eqnarray*}$$
as needed. If $y = \cons(c,u)$, we have
$$\begin{eqnarray*}
 &   & \beq(\snoc(a,\nil),\snoc(b,y)) \\
 &     \let{y = \cons(c,u)}
   = & \beq(\snoc(a,\nil),\snoc(b,\cons(c,u))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \beq(\snoc(a,\nil),\cons(c,\snoc(b,u))) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \beq(\cons(a,\nil),\cons(c,\snoc(b,u))) \\
 &     \href{@lists@#thm-list-eq-cons}
   = & \band(\beq(a,c),\beq(\nil,\snoc(b,u))) \\
 & = & \band(\beq(a,c),\bfalse) \\
 &     \href{@and@#thm-and-false-right}
   = & \bfalse \\
 &     \href{@and@#thm-and-false-right}
   = & \band(\beq(a,b),\bfalse) \\
 &     \href{@lists@#thm-list-eq-nil}
   = & \band(\beq(a,b),\beq(\nil,\cons(c,u))) \\
 &     \let{y = \cons(c,u)}
   = & \band(\beq(a,b),\beq(\nil,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$, $b$, and $y$ for some $x$ and let $d \in A$. We again consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(\snoc(a,\cons(d,x)),\snoc(b,y)) \\
 & = & \beq(\snoc(a,\cons(d,x)),\snoc(b,\nil)) \\
 & = & \beq(\cons(d,\snoc(a,x)),\cons(b,\nil)) \\
 &     \href{@lists@#thm-list-eq-cons}
   = & \band(\beq(d,b),\beq(\snoc(a,x),\nil)) \\
 & = & \band(\beq(d,b),\bfalse) \\
 &     \href{@and@#thm-and-false-right}
   = & \bfalse \\
 &     \href{@and@#thm-and-false-right}
   = & \band(\beq(a,b),\bfalse) \\
 & = & \band(\beq(a,b),\beq(\cons(d,x),\nil)) \\
 & = & \band(\beq(a,b),\beq(\cons(d,x),y))
\end{eqnarray*}$$
as needed. Suppose instead that $y = \cons(c,u)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \beq(\snoc(a,\cons(d,x)),\snoc(b,y)) \\
 &     \hyp{y = \cons(c,u)}
   = & \beq(\snoc(a,\cons(d,x)),\snoc(b,\cons(c,u))) \\
 & = & \beq(\cons(d,\snoc(a,x)),\snoc(b,\cons(c,u))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \beq(\cons(d,\snoc(a,x)),\cons(c,\snoc(b,u))) \\
 &     \href{@lists@#thm-list-eq-cons}
   = & \band(\beq(d,c),\beq(\snoc(a,x),\snoc(b,u))) \\
 &     \hyp{\beq(\snoc(a,x),\snoc(b,u)) = \band(\beq(a,b),\beq(x,u))}
   = & \band(\beq(d,c),\band(\beq(a,b),\beq(x,u))) \\
 & = & \band(\band(\beq(d,c),\beq(a,b)),\beq(x,u)) \\
 &     \href{@and@#thm-and-commutative}
   = & \band(\band(\beq(a,b),\beq(d,c)),\beq(x,u)) \\
 &     \href{@and@#thm-and-associative}
   = & \band(\beq(a,b),\band(\beq(d,c),\beq(x,u))) \\
 &     \href{@lists@#thm-list-eq-cons}
   = & \band(\beq(a,b),\beq(\cons(d,x),\cons(c,u))) \\
 &     \let{y = \cons(c,u)}
   = & \band(\beq(a,b),\beq(\cons(d,x),y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_snoc_eq :: (List t, Equal (t a), Equal a)
>   => t a -> Test (a -> a -> t a -> t a -> Bool)
> _test_snoc_eq _ =
>   testName "eq(snoc(a,x),snoc(b,y)) iff and(eq(a,b),eq(x,y))" $
>   \a b x y -> eq
>     (eq (snoc a x) (snoc b y))
>     (and (eq a b) (eq x y))

::::::::::::::::::::
::::::::::::::::::::

Now $\foldl(\ast)$ interacts with $\snoc$.

:::::: theorem :::::
[]{#thm-snoc-foldl}
We have $$\foldl(\varphi)(e,\snoc(a,x)) = \varphi(\foldl(\varphi)(e,x),a).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case we have
$$\begin{eqnarray*}
 &   & \foldl(\varphi)(e,\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \foldl(\varphi)(e,\cons(a,\nil)) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\varphi)(\varphi(e,a),\nil) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \varphi(e,a) \\
 &     \href{@foldl@#def-foldl-nil}
   = & \varphi(\foldl(\varphi)(e,\nil),a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $e$ and $a$ for some $x$, and let $b \in A$. Then we have
$$\begin{eqnarray*}
 &   & \foldl(\varphi)(e,\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \foldl(\varphi)(e,\cons(b,\snoc(a,x))) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\varphi)(\varphi(e,b),\snoc(a,x)) \\
 &     \hyp{\foldl(\varphi)(c,\snoc(a,x)) = \varphi(\foldl(\varphi)(c,x),a)}
   = & \varphi(\foldl(\varphi)(\varphi(e,b),x),a) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \varphi(\foldl(\varphi)(e,\cons(b,x)),a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_snoc_foldl :: (List t, Equal (t a), Equal a)
>   => t a -> Test ((a -> a -> a) -> a -> a -> t a -> Bool)
> _test_snoc_foldl _ =
>   testName "foldl(phi)(e,snoc(a,x)) == phi(foldl(phi)(e,x),a)" $
>   \phi e a x -> eq
>     (foldl phi e (snoc a x))
>     (phi (foldl phi e x) a)

::::::::::::::::::::
::::::::::::::::::::

And $\snoc$ is not $\nil$.

:::::: theorem :::::
[]{#thm-isnil-snoc}
We have $$\isnil(\snoc(a,x)) = \bfalse.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \isnil(\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \isnil(\cons(a,\nil)) \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \bfalse
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$; we have
$$\begin{eqnarray*}
 &   & \isnil(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \isnil(\cons(b,\snoc(a,x))) \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \bfalse
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_snoc_isnil :: (List t, Equal (t a), Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_snoc_isnil _ =
>   testName "eq(isnil(snoc(a,x)),false)" $
>   \a x -> eq (isNil (snoc a x)) false

::::::::::::::::::::
::::::::::::::::::::

Many interesting list functions can be implemented in terms of either $\foldr(\ast)(\ast)$ or $\foldl(\ast)$, and depending on the function, one may be preferable over the other. A useful question to ask is this: under what circumstances is a given right fold equivalent to a left fold? The next result provides a sufficient condition.

:::::: theorem :::::
Let $A$ and $B$ be sets, and suppose $\varphi : A \times B \rightarrow B$ has the property that $$\varphi(a,\varphi(b,e)) = \varphi(b,\varphi(a,e))$$ for all $a,b \in A$ and $e \in B$. Letting $\psi : B \times A \rightarrow B$ be given by $\psi(b,a) = \varphi(a,b)$, we have the following.

1. $\foldl(\psi)(e,\snoc(a,x)) = \foldl(\psi)(e,\cons(a,x))$.
2. $\foldr(e)(\varphi)(x) = \foldl(\psi)(e,x)$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \foldl(\psi)(e)(\cons(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \foldl(\psi)(e)(\snoc(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $e$ and $a$ for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \foldl(\psi)(e,\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \foldl(\psi)(e,\cons(b,\snoc(a,x))) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\psi)(\psi(e,b),\snoc(a,x)) \\
 &     \hyp{\foldl(\psi)(w)(\cons(a,x)) = \foldl(\psi)(w)(\snoc(a,x))}
   = & \foldl(\psi)(\psi(e,b),\cons(a,x)) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\psi)(\psi(\psi(e,b),a),x) \\
 & = & \foldl(\psi)(\varphi(a,\varphi(b,e)),x) \\
 & = & \foldl(\psi)(\varphi(b,\varphi(a,e)),x) \\
 & = & \foldl(\psi)(\psi(\psi(e,a),b),x) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\psi)(\psi(e,a),\cons(b,x)) \\
 &     \href{@foldl@#def-foldl-cons}
   = & \foldl(\psi)(e,\cons(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldr(e)(\varphi)(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & e \\
 & = & \foldl(\psi)(e,\nil)
\end{eqnarray*}$$
as needed. If $x = \cons(a,\nil)$, we have
$$\begin{eqnarray*}
 &   & \foldr(e)(\varphi)(\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \varphi(a,\foldr(e)(\varphi)(x)) \\
 & = & \varphi(a,\foldl(\psi)(e,x)) \\
 & = & \psi(\foldl(\psi)(e,x),a) \\
 &     \href{@snoc@#thm-snoc-foldl}
   = & \foldl(\psi)(e,\snoc(a,x)) \\
 & = & \foldl(\psi)(e,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

$\snoc$ interacts with $\head$.

:::::: theorem :::::
[]{#thm-snoc-head}
Let $A$ be a set. For all $a,b \in A$ and $x \in \lists{A}$ we have $$\head(\snoc(a,\snoc(b,x))) = \head(\snoc(b,x)).$$

::: proof ::::::::::
We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \head(\snoc(a,\snoc(b,\nil))) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \head(\snoc(a,\cons(b,\nil))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \head(\cons(b,\snoc(a,\nil))) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \rgt(b) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \head(\cons(b,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \head(\snoc(b,\nil))
\end{eqnarray*}$$
and if $x = \cons(c,y)$ we have
$$\begin{eqnarray*}
 &   & \head(\snoc(a,\snoc(b,x))) \\
 &     \let{x = \cons(c,y)}
   = & \head(\snoc(a,\snoc(b,\cons(c,y)))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \head(\snoc(a,\cons(c,\snoc(b,y)))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \head(\cons(c,\snoc(a,\snoc(b,y)))) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \rgt(c) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \head(\cons(c,\snoc(b,y))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \head(\snoc(b,\cons(c,y))) \\
 &     \let{x = \cons(c,y)}
   = & \head(\snoc(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_snoc_head :: (List t, Equal (t a), Equal a)
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_snoc_head _ =
>   testName "eq(head(snoc(a,snoc(b,xs))),head(snoc(b,xs)))" $
>   \a b x -> eq (head (snoc a (snoc b x))) (head (snoc b x))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_snoc ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   ) => Int -> Int -> t a -> IO ()
> _test_snoc size cases t = do
>   testLabel1 "snoc" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_snoc_nil t)
>   runTest args (_test_snoc_cons t)
>   runTest args (_test_snoc_eq t)
>   runTest args (_test_snoc_foldl t)
>   runTest args (_test_snoc_isnil t)
>   runTest args (_test_snoc_head t)

Main:

> main_snoc :: IO ()
> main_snoc = do
>   _test_snoc 20 100 (nil :: ConsList Bool)
>   _test_snoc 20 100 (nil :: ConsList Unary)
