---
title: Delete
author: nbloomf
date: 2017-05-27
tags: arithmetic-made-difficult, literate-haskell
slug: delete
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Delete
>   ( delete, _test_delete, main_delete
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import NaturalNumbers
> import Lists
> import Snoc
> import Reverse
> import Cat
> import PrefixAndSuffix
> import AllAndAny
> import Filter
> import Elt
> import Sublist
> import Unique

Today we'll establish a function $\delete$ that removes all copies of a given item from a list. $\delete$ is a special case of $\filter$.

:::::: definition ::
Let $A$ be a set, with $a \in A$. Define $\varphi : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(b,x) = \bif{\beq(a,b)}{x}{\cons(b,x)},$$ and define $\delete : A \rightarrow \lists{A}^{\lists{A}}$ by $$\delete(a) = \foldr(\nil)(\varphi).$$

In Haskell:

> delete :: (List t, Equal a) => a -> t a -> t a
> delete a = foldr nil phi
>   where
>     phi b x = if eq a b then x else cons b x

::::::::::::::::::::

Since $\delete(a)$ is defined as a fold, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\delete(a)$ is the unique map $f : \lists{A} \rightarrow \lists{A}$ satisfying the following equations for all $b \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(b,x)) = \bif{\beq(a,b)}{f(x)}{\cons(b,f(x))}
\end{array}\right.$$

::: test :::::::::::

> _test_delete_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> Bool)
> _test_delete_nil t =
>   testName "delete(a)(nil) == nil" $
>   \a -> eq (delete a nil) (nil `withTypeOf` t)
> 
> 
> _test_delete_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_delete_cons _ =
>   testName "delete(a)(cons(b,x)) == if(eq(a,b),delete(a)(x),cons(b,delete(a)(x)))" $
>   \a b x -> eq
>     (delete a (cons b x))
>     (if eq a b then delete a x else cons b (delete a x))

::::::::::::::::::::
::::::::::::::::::::

$\delete$ is a filter.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have $$\delete(a)(x) = \filter(\bnot(\beq(a,-)))(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(\bnot(\beq(a,-)))(\nil) \\
 & = & \nil \\
 & = & \delete(a)(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \filter(\bnot(\beq(a,-)))(\cons(b,x)) \\
 & = & \bif{\bnot(\beq(a,b))}{\cons(b,\filter(\bnot(\beq(a,-)))(x))}{\filter(\bnot(\beq(a,-)))(x)} \\
 & = & \bif{\bnot(\beq(a,b))}{\cons(b,\delete(a)(x))}{\delete(a)(x)} \\
 &     \href{@not@#thm-ifnot}
   = & \bif{\beq(a,b)}{\delete(a)(x)}{\cons(b,\delete(a)(x))} \\
 & = & \delete(a)(\cons(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_filter :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_filter _ =
>   testName "delete(a)(x) == filter(not(eq(a,-)))(x)" $
>   \a x -> eq (delete a x) (filter (\b -> not (eq a b)) x)

::::::::::::::::::::
::::::::::::::::::::

So $\delete$ commutes with $\filter$.

:::::: corollary :::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $a \in A$ and $x \in \lists{A}$, we have $$\delete(a)(\filter(p)(x)) = \filter(p)(\delete(a)(x)).$$

::: test :::::::::::

> _test_delete_filter_commute :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_delete_filter_commute _ =
>   testName "delete(a)(filter(p)(x)) == filter(p)(delete(a)(x))" $
>   \p a x -> eq (delete a (filter p x)) (filter p (delete a x))

::::::::::::::::::::
::::::::::::::::::::

And if $p(a) = \bfalse$, then $\filter(p)$ absorbs $\delete$.

:::::: theorem :::::
Let $A$ be a set with $p : A \rightarrow \bool$ a predicate. For all $a \in A$ and $x \in \lists{A}$, if $p(a) = \bfalse$ we have $$\delete(a)(\filter(p)(x)) = \filter(p)(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a)(\filter(p)(\nil)) \\
 &     \href{@filter@#cor-filter-nil}
   = & \delete(a)(\nil) \\
 & = & \nil \\
 &     \href{@filter@#cor-filter-nil}
   = & \filter(p)(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equatily holds for some $x$, and let $b \in A$. Note that if $p(b) = \btrue$, then $\beq(a,b)$ must be $\bfalse. Now
$$\begin{eqnarray*}
 &   & \delete(a)(\filter(p)(\cons(b,x))) \\
 &     \href{@filter@#cor-filter-cons}
   = & \delete(a)(\bif{p(b)}{\cons(b,\filter(p)(x))}{\filter(p)(x)}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{p(b)}{\delete(a)(\cons(b,\filter(p)(x)))}{\delete(a)(\filter(p)(x))} \\
 & = & \bif{p(b)}{\bif{\beq(a,b)}{\delete(a)(\filter(p)(x))}{\cons(b,\delete(a)(\filter(p)(x)))}}{\delete(a)(\filter(p)(x))} \\
 & = & \bif{p(b)}{\bif{\beq(a,b)}{\filter(p)(x)}{\cons(b,\filter(p)(x))}}{\filter(p)(x)} \\
 & = & \bif{p(b)}{\bif{\bfalse}{\filter(p)(x)}{\cons(b,\filter(p)(x))}}{\filter(p)(x)} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{p(b)}{\cons(b,\filter(p)(x))}{\filter(p)(x)} \\
 & = & \filter(p)(\cons(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_filter_absorb :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_delete_filter_absorb _ =
>   testName "if p(a) == false then delete(a)(filter(p)(x)) == filter(p)(x)" $
>   \p a x -> if isFalse (p a)
>     then eq (delete a (filter p x)) (filter p x)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\delete$ is idempotent.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\delete(a)(\delete(a)(x)) = \delete(a)(x).$$

::: proof ::::::::::
Note that, since $\filter(p)$ is idempotent for any predicate $p$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(a,x)) \\
 & = & \filter(\bnot(\beq(a,-)),\filter(\bnot(\beq(a,-)),x)) \\
 & = & \filter(\bnot(\beq(a,-)),x) \\
 & = & \delete(a,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_idempotent _ =
>   testName "delete(a)(delete(a)(x)) == delete(a)(x)" $
>   \a x -> eq (delete a (delete a x)) (delete a x)

::::::::::::::::::::
::::::::::::::::::::

$\delete$ can detect $\elt$.

:::::: theorem :::::
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then we have $$\beq(x,\delete(a,x)) = \bnot(\elt(a,x)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \beq(x,\delete(a,x)) \\
 & = & \beq(x,\filter(\bnot(\beq(a,-)),x)) \\
 & = & \all(\bnot(\beq(a,-)),x) \\
 & = & \bnot(\any(\beq(a,-),x)) \\
 & = & \bnot(\elt(a,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_eq_not_elt :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_eq_not_elt _ =
>   testName "eq(x,delete(a,x)) == not(elt(a,x))" $
>   \a x -> eq (eq x (delete a x)) (not (elt a x))

::::::::::::::::::::
::::::::::::::::::::

$\delete$ commutes with itself.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$ and $x \in \lists{A}$. Then $$\delete(a,\delete(b,x)) = \delete(b,\delete(a,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\nil)) \\
 & = & \delete(a,\nil) \\
 & = & \nil \\
 & = & \delete(b,\nil) \\
 & = & \delete(b,\delete(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $c \in A$. We consider four possibilities. If $c = a$ and $c = b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. If $c = a$ and $c \neq b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\cons(c,\delete(b,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. If $c \neq a$ and $c = b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\cons(c,\delete(a,x))) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. Finally, if $c \neq a$ and $c \neq b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\cons(c,\delete(b,x))) \\
 & = & \cons(c,\delete(a,\delete(b,x))) \\
 & = & \cons(c,\delete(b,\delete(a,x))) \\
 & = & \delete(b,\cons(c,\delete(a,x))) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_delete_commutative _ =
>   testName "delete(a)(delete(b)(x)) == delete(b)(delete(a)(x))" $
>   \a b x -> eq
>     (delete a (delete b x))
>     (delete b (delete a x))

::::::::::::::::::::
::::::::::::::::::::

$\delete$ removes elements.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$, we have $$\all(\bnot(\beq(a,-)))(\delete(a,x)) = \btrue.$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \all(\bnot(\beq(a,-)),\filter(\bnot(\beq(a,-)),x)) \\
 & = & \all(\bnot(\beq(a,-)),\delete(a,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_all_not_eq :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_all_not_eq _ =
>   testName "all(not(eq(a,-)))(delete(a)(x))" $
>   \a x -> all (\b -> not (eq a b)) (delete a x)

::::::::::::::::::::
::::::::::::::::::::

$\delete$ yields a sublist.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $a \in A$. Then $$\sublist(\delete(a,x),x) = \btrue.$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\filter(\bnot(\beq(a,-)),x),x) \\
 & = & \sublist(\delete(a,x),x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_sublist _ =
>   testName "sublist(delete(a)(x),x)" $
>   \a x -> sublist (delete a x) x

::::::::::::::::::::
::::::::::::::::::::

$\delete$ and $\unique$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $a \in A$. If $\unique(x) = \btrue$, then $\unique(\delete(a,x)) = \btrue$.

::: proof ::::::::::
Note that $\sublist(\delete(a)(x),x) = \btrue$, so that $\unique(\delete(a)(x)) = \btrue$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_unique :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_unique _ =
>   testName "if unique(x) then unique(delete(a)(x))" $
>   \a x -> if unique x then unique (delete a x) else true

::::::::::::::::::::
::::::::::::::::::::

$\delete$ interacts with $\elt$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $a,b \in A$. Then $$\elt(a,\delete(b,x)) = \bif{\beq(a,b)}{\bfalse}{\elt(a,x)}$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\delete(b,\nil)) \\
 & = & \elt(a,\nil) \\
 &     \href{@elt@#cor-elt-nil}
   = & \bfalse \\
 &     \href{@booleans@#thm-if-same}
   = & \bif{\beq(a,b)}{\bfalse}{\bfalse} \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,\nil)}
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $b$ for some $x$ and let $c \in A$. If $b = c$ and $a \neq c$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\delete(b,\cons(c,x))) \\
 & = & \elt(a,\delete(b,x)) \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,x)} \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,\cons(c,x))}.
\end{eqnarray*}$$
If $b = c$ and $a = c$, then
$$\begin{eqnarray*}
 &   & \elt(a,\delete(b,\cons(c,x))) \\
 & = & \elt(a,\delete(b,x)) \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,x)} \\
 & = & \bfalse \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,\cons(c,x))}.
\end{eqnarray*}$$
Suppose then that $b \neq c$. If $a = c$, then $a \neq b$, and we have
$$\begin{eqnarray*}
 &   & \elt(a,\delete(b,\cons(c,x))) \\
 & = & \elt(a,\cons(c,\delete(b,x))) \\
 &     \href{@elt@#cor-elt-cons}
   = & \bif{\beq(a,c)}{\btrue}{\elt(a,\delete(b,x))} \\
 & = & \btrue \\
 & = & \bif{\beq(a,c)}{\btrue}{\elt(a,x)} \\
 &     \href{@elt@#cor-elt-cons}
   = & \elt(a,\cons(c,x)) \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bfalse}{\elt(a,\cons(c,x))} \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,\cons(c,x))}.
\end{eqnarray*}$$
If $b \neq c$ and $a \neq c$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\delete(b,\cons(c,x))) \\
 & = & \elt(a,\cons(c,\delete(b,x))) \\
 & = & \elt(a,\delete(b,x)) \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,x)} \\
 & = & \bif{\beq(a,b)}{\bfalse}{\elt(a,\cons(c,x))}
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_elt :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_delete_elt _ =
>   testName "elt(a,delete(b)(x)) == if(eq(a,b),false,elt(a,x))" $
>   \a b x -> eq
>     (elt a (delete b x))
>     (if eq a b then false else elt a x)

::::::::::::::::::::
::::::::::::::::::::

$\delete$ preserves $\prefix$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$ and $a \in A$. If $\prefix(x,y) = \btrue$, then $\prefix(\delete(a)(x),\delete(a)(y)) = \btrue$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that $$\prefix(x,y) = \prefix(\nil,y) = \btrue$$ and
$$\begin{eqnarray*}
 &   & \prefix(\delete(a,x),\delete(a,y)) \\
 & = & \prefix(\delete(a,\nil),\delete(a,y)) \\
 & = & \prefix(\nil,\delete(a,y)) \\
 &     \href{@prefix-suffix@#cor-prefix-nil-left}
   = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $a$ and $y$ for some $x$ and let $b \in A$. Suppose further that $\prefix(\cons(b,x),y) = \btrue$. Now we must have $y = \cons(b,u)$ for some $u$ with $\prefix(x,u) = \btrue$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \prefix(\delete(a,\cons(b,x)),\delete(a,y)) \\
 & = & \prefix(\delete(a,\cons(b,x)),\delete(a,\cons(b,u))) \\
 & = & \prefix(\delete(a,x),\delete(a,u)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose instead that $a \neq b$; again by the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \prefix(\delete(a,\cons(b,x)),\delete(a,y)) \\
 & = & \prefix(\delete(a,\cons(b,x)),\delete(a,\cons(b,u))) \\
 & = & \prefix(\cons(b,\delete(a,x)),\cons(b,\delete(a,u))) \\
 & = & \prefix(\delete(a,x),\delete(a,u)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_delete_prefix _ =
>   testName "if prefix(x,y) then prefix(delete(a)(x),delete(a)(y))" $
>   \a x y -> if prefix x y then prefix (delete a x) (delete a y) else true

::::::::::::::::::::
::::::::::::::::::::

$\delete$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$ and $x \in \lists{A}$. Then we have $$\delete(a,\snoc(b,x)) = \bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))}.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \delete(a,\snoc(b,x)) \\
 & = & \delete(a,\snoc(b,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \delete(a,\cons(b,\nil)) \\
 & = & \bif{\beq(a,b)}{\delete(a,\nil)}{\cons(b,\delete(a,\nil))} \\
 & = & \bif{\beq(a,b)}{\delete(a,\nil)}{\cons(b,\nil)} \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \bif{\beq(a,b)}{\delete(a,\nil)}{\snoc(b,\nil)} \\
 & = & \bif{\beq(a,b)}{\delete(a,\nil)}{\snoc(b,\delete(a,\nil))} \\
 & = & \bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))}
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $b$ for some $x$ and let $c \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \delete(a,\snoc(b,\cons(c,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \delete(a,\cons(c,\snoc(b,x))) \\
 & = & \bif{\beq(a,c)}{\delete(a,\snoc(b,x))}{\cons(c,\delete(a,\snoc(b,x)))} \\
 & = & \bif{\beq(a,c)}{\bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))}}{\cons(c,\bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))})} \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{\beq(a,c)}{\bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))}}{\bif{\beq(a,b)}{\cons(c,\delete(a,x))}{\cons(c,\snoc(b,\delete(a,x)))}} \\
 & = & \bif{\beq(a,c)}{\bif{\beq(a,b)}{\delete(a,x)}{\snoc(b,\delete(a,x))}}{\bif{\beq(a,b)}{\cons(c,\delete(a,x))}{\snoc(b,\cons(c,\delete(a,x)))}} \\
 &     \href{@booleans@#thm-ifnest}
   = & \bif{\beq(a,b)}{\bif{\beq(a,c)}{\delete(a,x)}{\cons(c,\delete(a,x))}}{\bif{\beq(a,c)}{\snoc(b,\delete(a,x))}{\snoc(b,\cons(c,\delete(a,x)))}} \\
 & = & \bif{\beq(a,b)}{\delete(a,\cons(c,x))}{\bif{\beq(a,c)}{\snoc(b,\delete(a,x))}{\snoc(b,\cons(c,\delete(a,x)))}} \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{\beq(a,b)}{\delete(a,\cons(c,x))}{\snoc(b,\bif{\beq(a,c)}{\delete(a,x)}{\cons(c,\delete(a,x))})} \\
 & = & \bif{\beq(a,b)}{\delete(a,\cons(c,x))}{\snoc(b,\delete(a,\cons(c,x)))}
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_delete_snoc _ =
>   testName "delete(a)(snoc(b,x)) == if(eq(a,b),delete(a)(x),snoc(b,delete(a)(x)))" $
>   \a b x -> eq
>     (delete a (snoc b x))
>     (if eq a b then delete a x else snoc b (delete a x))

::::::::::::::::::::
::::::::::::::::::::

$\delete$ commutes with $\rev$.

:::::: theorem :::::
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then we have $$\delete(a,\rev(x)) = \rev(\delete(a,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \delete(a,\rev(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \delete(a,\nil) \\
 & = & \nil \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\nil) \\
 & = & \rev(\delete(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$ and let $b \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \delete(a,\rev(\cons(b,x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \delete(a,\snoc(b,\rev(x))) \\
 & = & \bif{\beq(a,b)}{\delete(a,\rev(x))}{\snoc(b,\delete(a,\rev(x)))} \\
 & = & \bif{\beq(a,b)}{\rev(\delete(a,x))}{\snoc(b,\rev(\delete(a,x)))} \\
 &     \href{@rev@#cor-rev-cons}
   = & \bif{\beq(a,b)}{\rev(\delete(a,x))}{\rev(\cons(b,\delete(a,x)))} \\
 &     \href{@booleans@#thm-iffunc}
   = & \rev(\bif{\beq(a,b)}{\delete(a,x)}{\cons(b,\delete(a,x))}) \\
 & = & \rev(\delete(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_delete_rev _ =
>   testName "delete(a)(rev(x)) == rev(delete(a)(x))" $
>   \a x -> eq (delete a (rev x)) (rev (delete a x))

::::::::::::::::::::
::::::::::::::::::::

$\delete$ distributes over $\cat$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$, we have $$\delete(a)(\cat(x,y)) = \cat(\delete(a)(x),\delete(a)(y)).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a)(\cat(x,\nil)) \\
 &     \href{@cat@#thm-cat-nil-right}
   = & \delete(a)(x) \\
 &     \href{@cat@#thm-cat-nil-right}
   = & \cat(\delete(a)(x),\nil) \\
 & = & \cat(\delete(a)(x),\delete(a)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $x$ for some  $y$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \delete(a)(\cat(x,\cons(b,y))) \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \delete(a)(\cat(\snoc(b,x),y)) \\
 & = & \cat(\delete(a)(\snoc(b,x)),\delete(a)(y)) \\
 & = & \cat(\bif{\beq(a,b)}{\delete(a)(x)}{\snoc(b,\delete(a)(x))},\delete(a)(y)) \\
 & = & \bif{\beq(a,b)}{\cat(\delete(a)(x),\delete(a)(y))}{\cat(\snoc(b,\delete(a)(x)),\delete(a)(y))} \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \bif{\beq(a,b)}{\cat(\delete(a)(x),\delete(a)(y))}{\cat(\delete(a)(x),\cons(b,\delete(a)(y)))} \\
 &     \href{@booleans@#thm-iffunc}
   = & \cat(\delete(a)(x),\bif{\beq(a,b)}{\delete(a)(y)}{\cons(b,\delete(a)(y))}) \\
 & = & \cat(\delete(a)(x),\delete(a)(\cons(b,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_delete_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_delete_cat _ =
>   testName "delete(a)(cat(x,y)) == cat(delete(a)(x),delete(a)(y))" $
>   \a x y -> eq
>     (delete a (cat x y))
>     (cat (delete a x) (delete a y))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_delete ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => Int -> Int -> t a -> IO ()
> _test_delete size cases t = do
>   testLabel1 "delete" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_delete_nil t)
>   runTest args (_test_delete_cons t)
>   runTest args (_test_delete_filter t)
>   runTest args (_test_delete_filter_commute t)
>   runTest args (_test_delete_filter_absorb t)
>   runTest args (_test_delete_idempotent t)
>   runTest args (_test_delete_eq_not_elt t)
>   runTest args (_test_delete_commutative t)
>   runTest args (_test_delete_all_not_eq t)
>   runTest args (_test_delete_sublist t)
>   runTest args (_test_delete_unique t)
>   runTest args (_test_delete_elt t)
>   runTest args (_test_delete_prefix t)
>   runTest args (_test_delete_snoc t)
>   runTest args (_test_delete_rev t)
>   runTest args (_test_delete_cat t)

Main:

> main_delete :: IO ()
> main_delete = do
>   _test_delete 20 100 (nil :: ConsList Bool)
>   _test_delete 20 100 (nil :: ConsList Unary)
