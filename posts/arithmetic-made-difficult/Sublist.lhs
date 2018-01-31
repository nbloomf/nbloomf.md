---
title: Sublist
author: nbloomf
date: 2017-05-23
tags: arithmetic-made-difficult, literate-haskell
slug: sublist
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Sublist
>   ( sublist, _test_sublist, main_sublist
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Tuples
> import NaturalNumbers
> import Plus
> import LessThanOrEqualTo
> import Lists
> import HeadAndTail
> import DoubleFold
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat

Today we'll nail down what it means for one list to be a *sublist* of another. Intuitively, a sublist is "part of" some larger list; but there is some ambiguity here: does the sublist have to be contiguous in the larger list? For example, it seems clear that $$\langle b, c \rangle$$ should be considered a sublist of $$\langle a, b, c, d, e \rangle$$ while $$\langle e, g \rangle$$ should not. But what about $$\langle a, c \rangle,$$ or even $$\langle c, a \rangle$$ for that matter? First, lists are inherently ordered, so the "sublist" idea should reflect this -- sublists have to respect the order of their superlists. On the other hand, it is less crucial that sublists be contiguous in their superlists. Contiguous sublists are still interesting though (for reasons we'll see later), so we will single them out as infixes (analogous to prefixes and suffixes).

So we have two related but distinct concepts, sublists and infixes, that will need to be dealt with separately. We'll define two boolean functions, $\sublist$ and $\infix$, which detect when one list is a sublist or infix (respectively) of another. We'll start with $\sublist$. This function should have a signature like $$\lists{A} \times \lists{A} \rightarrow \bool.$$ Double fold was made for situations like this, so we could try to define $\sublist$ as a double fold like $$\sublist(x,y) = \dfoldr{\delta}{\psi}{\chi}(x,y)$$ But if we do this, assuming some reasonable behavior for $\sublist$, we get stuck! (Try it!) What happens is that the fold eats $x$, but when $x$ and $y$ are not nil but have different first items we need the recursion to un-eat the $x$ parameter. The fix is to instead fold on $y$ like $$\sublist(x,y) = \dfoldr{\delta}{\psi}{\chi}(y,x).$$

Blah blah, define $\sublist$ like this.

:::::: definition ::
Let $A$ be a set. Define $\psi : A \times \bool \rightarrow \bool$ by $$\psi(a,p) = \btrue,$$ and $\chi : A \times A \times \lists{A} \times \bool \times \bool \rightarrow \lists{A}$ by $$\chi(a,b,y,p,q) = \bif{\beq(a,b)}{p}{q}.$$ We now define $\sublist : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\sublist(x,y) = \dfoldr{\isnil}{\psi}{\chi}(y,x).$$

In Haskell:

> sublist :: (List t, Equal a) => t a -> t a -> Bool
> sublist x y = dfoldr delta psi chi y x
>   where
>     delta y = isNil y
>     psi _ _ = true
>     chi a b _ p q = if eq a b then p else q

::::::::::::::::::::

Since $\sublist$ is defined as a $\dfoldr{\ast}{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\sublist$ is the unique map $f : \lists{A} \times \lists{A} \rightarrow \bool$ satisfying the following system of functional equations for all $a,b \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(x,\nil) = \isnil(x) \\
 f(\nil,\cons(b,y)) = \btrue \\
 f(\cons(a,x),\cons(b,y)) = \bif{\beq(a,b)}{\sublist(x,y)}{\sublist(\cons(a,x),y)}
\end{array}\right.$$

::: test :::::::::::

> _test_sublist_list_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_sublist_list_nil _ =
>   testName "sublist(x,nil) == isNil(x)" $
>   \x -> eq (sublist x nil) (isNil x)
> 
> 
> _test_sublist_nil_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_sublist_nil_cons _ =
>   testName "sublist(nil,cons(b,y)) == true" $
>   \b y -> eq (sublist nil (cons b y)) true
> 
> 
> _test_sublist_cons_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> a -> t a -> Bool)
> _test_sublist_cons_cons _ =
>   testName "sublist(cons(a,x),cons(b,y)) == if(eq(a,b),sublist(x,y),sublist(cons(a,x),y))" $
>   \a x b y -> eq
>     (sublist (cons a x) (cons b y))
>     (if eq a b then sublist x y else sublist (cons a x) y)

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ is reflexive.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ we have $\sublist(x,x)$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, certainly $$\sublist(\nil,\nil) = \btrue.$$ For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),\cons(a,x)) \\
 & = & \bif{\beq(a,a)}{\sublist(x,x)}{\sublist(\cons(a,x),x)} \\
 & = & \sublist(x,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_reflexive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_sublist_reflexive _ =
>   testName "sublist(x,x) == true" $
>   \x -> eq (sublist x x) true

::::::::::::::::::::
::::::::::::::::::::

$\snoc$ is cancellative inside $\sublist$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$, we have the following.

1. $\sublist(nil,\snoc(b,y)) = \btrue$.
2. $\sublist(\snoc(a,x),\snoc(a,y)) = \sublist(x,y)$.

::: proof ::::::::::
1. There are two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\nil,\snoc(b,\nil)) \\
 & = & \sublist(\nil,\cons(b,\nil)) \\
 & = & \btrue,
\end{eqnarray*}$$
and if $y = \cons(c,u)$ we have
$$\begin{eqnarray*}
 &   & \sublist(\nil,\snoc(b,\cons(c,u))) \\
 & = & \sublist(\nil,\cons(c,\snoc(b,u))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that $\sublist(x,y) = \btrue$. We show that $\sublist(\snoc(a,\nil),\snoc(a,y)) = \btrue$ by list induction on $y$. For the base case $y = \nil$, we have $$\sublist(\snoc(a,\nil),\snoc(a,\nil)) = \btrue$$ by reflexivity. For the inductive step (on $y$), suppose the equality holds for some $y$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\nil),\snoc(a,\cons(b,y))) \\
 & = & \sublist(\cons(a,\nil),\cons(b,\snoc(a,y))) \\
 & = & \bif{\beq(a,b)}{\sublist(\nil,\snoc(a,y))}{\sublist(\cons(a,\nil),\snoc(a,y))} \\
 & = & \bif{\beq(a,b)}{\btrue}{\sublist(\snoc(a,\nil),\snoc(a,y))} \\
 & = & \bif{\beq(a,b)}{\btrue}{\btrue} \\
 &     \href{@booleans@#thm-if-same}
   = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step (on $x$), suppose the equality holds for some $x$ and let $c \in A$. We need to show that $$\sublist(\cons(c,x),y) = \sublist(\snoc(a,\cons(c,x)),\snoc(a,y))$$ for all $y$; we again proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),y) \\
 & = & \sublist(\cons(c,x),\nil) \\
 & = & \isnil(\cons(c,x)) \\
 & = & \bfalse,
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\cons(c,x)),\snoc(a,y)) \\
 & = & \sublist(\snoc(a,\cons(c,x)),\snoc(a,\nil)) \\
 & = & \sublist(\cons(c,\snoc(a,x)),\cons(a,\nil)) \\
 & = & \bif{\beq(c,a)}{\sublist(\snoc(a,x),\nil)}{\sublist(\cons(c,\snoc(a,x)),\nil)} \\
 & = & \bif{\beq(c,a)}{\bfalse}{\bfalse} \\
 &     \href{@booleans@#thm-if-same}
   = & \bfalse
\end{eqnarray*}$$
as needed. For the inductive step (on $y$), suppose we have $$\sublist(\cons(c,x),y) = \sublist(\snoc(a,\cons(c,x)),\snoc(a,y))$$ for some $y$, and let $b \in A$. Using both the outer and nested inductive hypotheses we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\cons(c,x)),\snoc(a,\cons(b,y))) \\
 & = & \sublist(\cons(c,\snoc(a,x)),\cons(b,\snoc(a,y))) \\
 & = & \bif{\beq(c,b)}{\sublist(\snoc(a,x),\snoc(a,y))}{\sublist(\cons(c,\snoc(a,x)),\snoc(a,y))} \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\snoc(a,\cons(c,x)),\snoc(a,y))} \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \sublist(\cons(c,x),\cons(b,y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_nil_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_sublist_nil_snoc _ =
>   testName "sublist(nil,snoc(b,y)) == true" $
>   \b y -> eq (sublist nil (snoc b y)) true
> 
> 
> _test_sublist_snoc_cancel :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_sublist_snoc_cancel _ =
>   testName "sublist(snoc(a,x),snoc(a,y)) == sublist(x,y)" $
>   \a x y -> eq (sublist (snoc a x) (snoc a y)) (sublist x y)

::::::::::::::::::::
::::::::::::::::::::

$\cat$ is cancellative inside $\sublist$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have the following.

1. $\sublist(\cat(z,x),\cat(z,y)) = \sublist(x,y)$.
2. $\sublist(\cat(x,z),\cat(y,z)) = \sublist(x,y)$.

::: proof ::::::::::
1. We proceed by list induction on $z$. For the base case $z = \nil$, of course
$$\begin{eqnarray*}
 &   & \sublist(\cat(\nil,x),\cat(\nil,y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ and $y$ for some $z$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cat(\cons(a,z),x),\cat(\cons(a,z),y)) \\
 & = & \sublist(\cons(a,\cat(z,x)),\cons(a,\cat(z,y))) \\
 & = & \bif{\beq(a,a)}{\sublist(x,y)}{\sublist(\cons(a,x),y)} \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
2. We proceed by snoc induction on $z$. For the base case $z = \nil$, of course
$$\begin{eqnarray*}
 &   & \sublist(\cat(x,\nil),\cat(y,\nil)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ and $y$ for some $z$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cat(x,\snoc(a,z)),\cat(y,\snoc(a,z))) \\
 & = & \sublist(\snoc(a,\cat(x,z)),\snoc(a,\cat(y,z))) \\
 & = & \sublist(\cat(x,z),\cat(y,z)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_cat_left_cancel :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_cat_left_cancel _ =
>   testName "sublist(cat(z,x),cat(z,y)) == sublist(x,y)" $
>   \x y z -> eq (sublist (cat z x) (cat z y)) (sublist x y)
> 
> 
> _test_sublist_cat_right_cancel :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_cat_right_cancel _ =
>   testName "sublist(cat(x,z),cat(y,z)) == sublist(x,y)" $
>   \x y z -> eq (sublist (cat x z) (cat y z)) (sublist x y)

::::::::::::::::::::
::::::::::::::::::::

Sublist conditionally interacts with $\cons$. This one seems like it should be obvious, but the only proof I could find was kind of complicated -- nested induction of two statements at once.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$ and $x,y \in \lists{A}$. Then we have the following.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cons(b,y)) = \btrue$.
2. If $\sublist(\cons(a,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.

::: proof ::::::::::
This proof is a little different: we will prove both (1) and (2) simultaneously by list induction on $x$. For the base case $x = \nil$, to see (1), note that for all $b \in A$ and $y \in \lists{A}$ we have $$\sublist(\nil,y) = \btrue = \sublist(\nil,\cons(b,y))$$ as needed. To see (2), note that $\sublist(\nil,y)$, so the implication holds regardless of the values of $a$ and $y$.

For the inductive step, suppose both (1) and (2) hold for all $a,b \in A$ and $y \in \lists{A}$ for some $x \in \lists{A}$, and let $c \in A$.

Now we claim that (1) holds with $x$ replaced by $\cons(c,x)$; that is, for all $b \in A$ and $y \in \lists{A}$, if $\sublist(\cons(c,x),y) = \btrue$ then $\sublist(\cons(c,x),\cons(b,y)) = \btrue$. To this end, suppose we have $\sublist(\cons(c,x),y) = \btrue$. Using part (2) of the induction hypothesis, we have $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),\cons(b,y)) \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \bif{\beq(c,b)}{\btrue}{\btrue} \\
 &     \href{@booleans@#thm-if-same}
   = & \btrue
\end{eqnarray*}$$
as needed.

Next we claim that (2) holds with $x$ replaced by $\cons(c,x)$. That is, for all $a \in A$ and $y \in \lists{A}$, if $\sublist(\cons(a,\cons(c,x)),y) = \btrue$ then $\sublist(\cons(c,x),y) = \btrue$. We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,\cons(c,x)),y) \\
 & = & \sublist(\cons(a,\cons(c,x)),\nil) \\
 & = & \isnil(\cons(a,\cons(c,x))) \\
 & = & \bfalse;
\end{eqnarray*}$$
thus the implication (2) holds vacuously.

For the inductive step, suppose we have $y \in \lists{A}$ such that, for all $a \in A$, if $\sublist(\cons(a,\cons(c,x)),y) = \btrue$ then $\sublist(\cons(c,x),y) = \btrue$. Let $d \in A$, and suppose $$\sublist(\cons(a,\cons(c,x)),\cons(d,y)) = \btrue.$$

We consider two possibilities. If $a \neq d$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,\cons(c,x)),\cons(d,y)) \\
 & = & \sublist(\cons(a,\cons(c,x)),y).
\end{eqnarray*}$$
By the (nested) induction hypothesis, we have $$\sublist(\cons(c,x),y) = \btrue.$$ We established above that this implies $$\sublist(\cons(c,x),\cons(d,y)) = \btrue$$ as needed. Now suppose instead that $a = d$. Then
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,\cons(c,x)),\cons(d,y)) \\
 & = & \sublist(\cons(c,x),y).
\end{eqnarray*}$$
By part (2) of the (outer) induction hypothesis, we have $$\sublist(x,y) = \btrue.$$ Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),\cons(d,y)) \\
 & = & \bif{\beq(c,d)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \bif{\beq(c,d)}{\btrue}{\btrue} \\
 &     \href{@booleans@#thm-if-same}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_cons_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_sublist_cons_right _ =
>   testName "sublist(x,y) ==> sublist(x,cons(a,y))" $
>   \a x y -> if sublist x y
>     then sublist x (cons a y)
>     else true
> 
> 
> _test_sublist_cons_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_sublist_cons_left _ =
>   testName "sublist(cons(a,x),y) ==> sublist(x,y)" $
>   \a x y -> if sublist (cons a x) y
>     then sublist x y
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts with $\length$.

:::::: theorem :::::
Let $A$ be a set, with $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$, then $\nleq(\length(x),\length(y))$.

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, note that $\length(y) = \zero$. Now if
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(x,\nil) \\
 & = & \isnil(x),
\end{eqnarray*}$$
we have $x = \nil$, so that $\length(x) = \zero$. Thus
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\zero,\zero) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$ for some $y$, and let $b \in A$. We consider two cases for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\nil,\cons(b,y)) \\
 & = & \btrue,
\end{eqnarray*}$$
and furthermore
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(\cons(b,y))) \\
 & = & \nleq(\length(\nil),\length(\cons(b,y))) \\
 & = & \nleq(\zero,\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose then that $x = \cons(a,u)$, and suppose further that $\sublist(x,\cons(b,y)) = \btrue$. We have two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y).
\end{eqnarray*}$$
By the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(u),\length(y)) \\
 & = & \nleq(\next(\length(u)),\next(\length(y))) \\
 & = & \nleq(\length(\cons(a,u)),\length(\cons(b,y))) \\
 & = & \nleq(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(\cons(a,u),y).
\end{eqnarray*}$$
By the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\cons(a,u)),\length(y)) \\
 & = & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\length(x),\next(\length(y))) \\
 & = & \nleq(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_length :: (List t, Equal a, Equal (t a), Natural n)
>   => t a -> n -> Test (t a -> t a -> Bool)
> _test_sublist_length _ k =
>   testName "if sublist(x,y) then leq(length(x),length(y))" $
>   \x y -> if sublist x y
>     then leq ((length x) `withTypeOf` k) (length y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ is antisymmetric.

:::::: theorem :::::
Let $A$ be a set, and $x,y \in \lists{A}$. We have $\sublist(x,y)$ and $\sublist(y,x)$ if and only if $x = y$.

::: proof ::::::::::
The "if" direction is trivial. To see the "only if" direction we proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(y,x) \\
 & = & \sublist(y,\nil) \\
 & = & \isnil(y),
\end{eqnarray*}$$
so that $y = \nil = x$ as claimed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. We now consider two possibilities for $y$. If $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),y) \\
 & = & \sublist(\cons(a,x),\nil) \\
 & = & \isnil(\cons(a,x)) \\
 & = & \bfalse.
\end{eqnarray*}$$
Thus the implication holds vacuously. Suppose instead that $y = \cons(b,v)$, and suppose further that $\sublist(\cons(a,x),\cons(b,v))$ and $\sublist(\cons(b,v),\cons(a,x))$ are both $\btrue$. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(a,x)) \\
 & = & \sublist(\cons(b,v),x) \\
 & = & \sublist(y,x).
\end{eqnarray*}$$
But now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\cons(a,x)),\length(y)) \\
 & = & \nleq(\next(\length(x)),\length(y))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(y),\length(x));
\end{eqnarray*}$$
by transitivity, we thus also have $$\nleq(\next(\length(x)),\length(x)),$$ a contradiction. So in fact $a = b$. Thus we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(a,x)) \\
 & = & \sublist(v,x)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,x),\cons(b,v)) \\
 & = & \sublist(x,v),
\end{eqnarray*}$$
so that (by the induction hypothesis) we have $x = v$, and so
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cons(b,v) \\
 & = & y
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_antisymmetric :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_sublist_antisymmetric _ =
>   testName "and(sublist(x,y),sublist(y,x)) == eq(x,y)" $
>   \x y -> eq (and (sublist x y) (sublist y x)) (eq x y)

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ is transitive.

:::::: theorem :::::
Let $A$ be a set, with $x,y,z \in \lists{A}$. If $\sublist(x,y)$ and $\sublist(y,z)$, then $\sublist(x,z)$.

::: proof ::::::::::
We proceed by list induction on $z$. For the base case $z = \nil$, note that if $\sublist(y,z) = \btrue$ we have $y = \nil$, and then if $\sublist(x,y) = \btrue$ we also have $x = \nil$. In particular, $\sublist(x,z) = \btrue$ as needed. For the inductive step, suppose the implication holds for all $x$ and $y$ for some $z$, and let $c \in A$. Suppose further that $\sublist(x,y)$ and $\sublist(y,\cons(c,z))$. We consider two cases for $y$. If $y = \nil$, note that $x = \nil$, so we have $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $y = \cons(b,v)$. If $b \neq c$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(c,z)) \\
 & = & \sublist(\cons(b,v),z);
\end{eqnarray*}$$
by the inductive hypothesis, we have $\sublist(x,z)$, so that $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $b = c$; then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(c,z)) \\
 & = & \sublist(v,z).
\end{eqnarray*}$$
We consider two cases for $x$; if $x = \nil$, then $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $x = \cons(a,u)$. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,u),\cons(b,v)) \\
 & = & \sublist(\cons(a,u),v),
\end{eqnarray*}$$
and by the inductive hypothesis, $\sublist(x,z)$, so that $\sublist(x,\cons(c,z))$ as claimed. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,u),\cons(b,v)) \\
 & = & \sublist(u,v).
\end{eqnarray*}$$
By the inductive hypothesis, $\sublist(u,z)$, so that $\sublist(x,\cons(c,z))$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_transitive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_transitive _ =
>   testName "if and(sublist(x,y),sublist(y,z)) then sublist(x,z)" $
>   \x y z -> if and (sublist x y) (sublist y z)
>     then sublist x z
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ is compatible with $\cat$.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $x,y,u,v \in \lists{A}$. If $\sublist(x,u)$ and $\sublist(y,v)$, then $\sublist(\cat(x,y),\cat(u,v))$.

::: proof ::::::::::
If $\sublist(x,u) = \btrue$, then $\sublist(\cat(x,y),\cat(u,y)) = \btrue$. Similarly, if $\sublist(y,v) = \btrue$, then $\sublist(\cat(u,y),\cat(u,v)) = \btrue$. By transitivity, we have $$\sublist(\cat(x,y),cat(u,v)) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_cat_compatible :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> t a -> Bool)
> _test_sublist_cat_compatible _ =
>   testName "if and(sublist(x,y),sublist(u,v)) then sublist(cat(x,u),cat(y,v))" $
>   \x y u v -> if and (sublist x y) (sublist u v)
>     then sublist (cat x u) (cat y v)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \bif{\beq(a,b)}{\sublist(x,y)}{\sublist(\snoc(a,x),y)}.$$

::: proof ::::::::::
We've already seen that $$\sublist(\snoc(a,x),\snoc(a,y)) = \sublist(x,y).$$ So it suffices to show that if $a \neq b$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \sublist(\snoc(a,x),y).$$ We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),y) \\
 & = & \sublist(\snoc(a,x),\nil) \\
 & = & \isnil(\snoc(a,x)) \\
 & = & \bfalse.
\end{eqnarray*}$$
We will now show that $\sublist(\snoc(a,x),\snoc(b,\nil)) = \bfalse$ by considering two cases for $x$. If $x = nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\nil)) \\
 & = & \sublist(\snoc(a,\nil),\snoc(b,\nil)) \\
 & = & \sublist(\cons(a,\nil),\cons(b,\nil)) \\
 & = & \sublist(\cons(a,\nil),\nil) \\
 & = & \isnil(\cons(a,\nil)) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. If $x = \cons(c,u)$ and $\sublist(\snoc(a,x),\snoc(b,\nil)) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\snoc(a,x)),\length(\snoc(b,\nil))) \\
 & = & \nleq(\next(\length(x)),\next(\length(\nil))) \\
 & = & \nleq(\next(\length(\cons(c,u))),\next(\zero)) \\
 & = & \nleq(\next(\next(\length(u))),\next(\zero)) \\
 & = & \bfalse,
\end{eqnarray*}$$
a contradiction.

Now for the inductive step, suppose the equality holds for some $y$. That is, for all $a \neq b$ and all $x$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \sublist(\snoc(a,x),y).$$ Let $d \in A$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\snoc(a,\nil),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\cons(a,\nil),\cons(d,\snoc(b,y))) \\
 & = & \bif{\beq(a,d)}{\sublist(\nil,\snoc(b,y))}{\sublist(\cons(a,\nil),\snoc(b,y))} \\
 & = & \bif{\beq(a,d)}{\btrue}{\sublist(\snoc(a,\nil),\snoc(b,y))} \\
 & = & \bif{\beq(a,d)}{\btrue}{\sublist(\snoc(a,\nil),y)} \\
 & = & \bif{\beq(a,d)}{\sublist(\nil,y)}{\sublist(\cons(a,\nil),y)} \\
 & = & \sublist(\cons(a,\nil),\cons(d,y)) \\
 & = & \sublist(\snoc(a,\nil),\cons(d,y))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(c,u)$. Now we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\snoc(a,\cons(c,u)),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\cons(c,\snoc(a,u)),\cons(d,\snoc(b,y))) \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),\snoc(b,y))}{\sublist(\cons(c,\snoc(a,u)),\snoc(b,y))} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\snoc(a,\cons(c,u)),\snoc(b,y))} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\snoc(a,\cons(c,u)),y)} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\cons(c,\snoc(a,u)),y)} \\
 & = & \sublist(\cons(c,\snoc(a,u)),\cons(d,y)) \\
 & = & \sublist(\snoc(a,\cons(c,u)),\cons(d,y)) \\
 & = & \sublist(\snoc(a,x),\cons(d,y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_snoc_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> t a -> Bool)
> _test_sublist_snoc_snoc _ =
>   testName "sublist(snoc(a,x),snoc(b,y)) == if(eq(a,b),sublist(x,y),sublist(snoc(a,x),y))" $
>   \a b x y -> eq
>     (sublist (snoc a x) (snoc b y))
>     (if eq a b then sublist x y else sublist (snoc a x) y)

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts with $\rev$:

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\sublist(x,y) = \sublist(\rev(x),\rev(y)).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,y) \\
 & = & \sublist(x,\nil) \\
 & = & \isnil(x) \\
 & = & \isnil(\rev(x)) \\
 & = & \sublist(\rev(x),\nil) \\
 & = & \sublist(\rev(x),\rev(\nil)) \\
 & = & \sublist(\rev(x),\rev(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $y$ and let $b \in A$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\nil,\cons(b,y)) \\
 & = & \btrue \\
 & = & \sublist(\nil,\rev(\cons(b,y))) \\
 & = & \sublist(\rev(\nil),\rev(\cons(b,y))) \\
 & = & \sublist(\rev(x),\rev(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,w)$. Then we have
$$\begin{eqnarray*}
 & = & \sublist(\rev(x),\rev(\cons(b,y))) \\
 & = & \sublist(\rev(\cons(a,w)),\rev(\cons(b,y))) \\
 & = & \sublist(\snoc(a,\rev(w)),\snoc(b,\rev(y))) \\
 & = & \bif{\beq(a,b)}{\sublist(\rev(w),\rev(y))}{\sublist(\snoc(a,\rev(w)),\rev(y))} \\
 & = & \bif{\beq(a,b)}{\sublist(w,y)}{\sublist(\rev(\cons(a,w)),\rev(y))} \\
 & = & \bif{\beq(a,b)}{\sublist(w,y)}{\sublist(\cons(a,w),y)} \\
 & = & \sublist(\cons(a,w),\cons(b,y)) \\
 & = & \sublist(x,\cons(b,y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_sublist_rev _ =
>   testName "sublist(x,y) == sublist(rev(x),rev(y))" $
>   \x y -> eq (sublist x y) (sublist (rev x) (rev y))

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts conditionally with $\snoc$ in one argument.

:::::: theorem :::::
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. Then we have the following.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\snoc(a,y)) = \btrue$.
2. If $\sublist(\snoc(a,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.

::: proof ::::::::::
1. Suppose $\sublist(x,y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(\rev(x),\cons(a,\rev(y))) \\
 & = & \sublist(\rev(x),\rev(\snoc(a,y))) \\
 & = & \sublist(x,\snoc(a,y))
\end{eqnarray*}$$
as claimed.
2. Suppose $\sublist(\snoc(a,x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\snoc(a,x),y) \\
 & = & \sublist(\rev(\snoc(a,x)),\rev(y)) \\
 & = & \sublist(\cons(a,\rev(x)),\rev(y)) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_snoc_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_sublist_snoc_right _ =
>   testName "sublist(x,y) ==> sublist(x,snoc(a,y))" $
>   \a x y -> if sublist x y
>     then sublist x (snoc a y)
>     else true
> 
> 
> _test_sublist_snoc_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_sublist_snoc_left _ =
>   testName "sublist(snoc(a,x),y) ==> sublist(x,y)" $
>   \a x y -> if sublist (snoc a x) y
>     then sublist x y
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts conditionally with $\cat$ in one argument.

:::::: theorem :::::
Let $A$ be a set, with $x,y,z \in \lists{A}$.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cat(z,y)) = \btrue$.
2. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cat(y,z)) = \btrue$.
3. If $\sublist(\cat(z,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.
4. If $\sublist(\cat(x,z),y) = \btrue$, then $\sublist(x,y) = \btrue$.

::: proof ::::::::::
1. We proceed by list induction on $z$. For the base case $z = \nil$, suppose $\sublist(x,y) = \btrue$. Then
$$\begin{eqnarray*}
 &   & \sublist(x,\cat(z,y)) \\
 & = & \sublist(x,\cat(\nil,y)) \\
 & = & \sublist(x,y) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $z$ and let $a \in A$. Suppose further that $\sublist(x,y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(x,\cat(z,y)) \\
 & = & \sublist(x,\cons(a,\cat(z,y))) \\
 & = & \sublist(x,\cat(\cons(a,z),y))
\end{eqnarray*}$$
as needed.
2. Suppose $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(\rev(x),\cat(\rev(z),\rev(y))) \\
 & = & \sublist(\rev(x),\rev(\cat(y,z))) \\
 & = & \sublist(x,\cat(y,z))
\end{eqnarray*}$$
as claimed.
3. We proceed by list induction on $z$. For the base case $z = \nil$, suppose $\sublist(\cat(z,x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(z,x),y) \\
 & = & \sublist(\cat(\nil,x),y) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$ and $y$ for some $z$ and let $a \in A$. Suppose further that $\sublist(\cat(\cons(a,z),x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(\cons(a,z),x),y) \\
 & = & \sublist(\cons(a,\cat(z,x)),y) \\
 & = & \sublist(\cat(z,x),y) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
4. Suppose $\sublist(\cat(x,z),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(x,z),y) \\
 & = & \sublist(\rev(\cat(x,z)),\rev(y)) \\
 & = & \sublist(\cat(\rev(z),\rev(x)),\rev(y)) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_left_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_left_cat_right _ =
>   testName "if sublist(x,y) then sublist(x,cat(z,y))" $
>   \x y z -> if sublist x y
>     then sublist x (cat z y)
>     else true
> 
> 
> _test_sublist_right_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_right_cat_right _ =
>   testName "if sublist(x,y) then sublist(x,cat(y,z))" $
>   \x y z -> if sublist x y
>     then sublist x (cat y z)
>     else true
> 
> 
> _test_sublist_left_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_left_cat_left _ =
>   testName "if sublist(cat(z,x),y) then sublist(x,y)" $
>   \x y z -> if sublist (cat z x) y
>     then sublist x y
>     else true
> 
> 
> _test_sublist_right_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_sublist_right_cat_left _ =
>   testName "if sublist(cat(x,z),y) then sublist(x,y)" $
>   \x y z -> if sublist (cat x z) y
>     then sublist x y
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts with $\map(f)$ when $f$ is injective.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ injective. For all $x,y \in \lists{A}$ we have $$\sublist(\map(f)(x),\map(f)(y)) = \sublist(x,y).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(x),\map(f)(\nil)) \\
 & = & \sublist(\map(f)(x),\nil) \\
 & = & \isnil(\map(f)(x)) \\
 & = & \isnil(x) \\
 & = & \sublist(x,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for all $x$ for some $y$, and let $b \in A$. We have two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(\nil),\map(f)(\cons(b,y))) \\
 & = & \sublist(\nil,\map(f)(\cons(b,y))) \\
 & = & \btrue \\
 & = & \sublist(\nil,\cons(b,y))
\end{eqnarray*}$$
as claimed. Suppose instead that $x = \cons(a,u)$. Note that since $f$ is injective we have $\beq(f(a),f(b)) = \beq(a,b)$; then we have
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(\cons(a,u)),\map(f)(\cons(b,y))) \\
 & = & \sublist(\cons(f(a),\map(f)(u)),\cons(f(b))(\map(f)(y))) \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(\map(f)(u),\map(f)(y))}{\sublist(\cons(f(a),\map(f)(u)),\map(f)(y))} \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(u,y)}{\sublist(\map(f)(\cons(a,u)),\map(f)(y))} \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(u,y)}{\sublist(\cons(a,u),y)} \\
 & = & \bif{\beq(a,b)}{\sublist(u,y)}{\sublist(\cons(a,u),y)} \\
 & = & \sublist(\cons(a,u),\cons(b,y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts with $\filter$.

:::::: theorem :::::
Let $A$ be a set, let $p : A \rightarrow \bool$, and let $x \in \lists{A}$. Then we have $$\sublist(\filter(p,x),x) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,x),x) \\
 & = & \sublist(\filter(p,\nil),\nil) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $p$ for some $x$ and let $a \in A$. We consider two possibilities. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,\cons(a,x)),\cons(a,x)) \\
 & = & \sublist(\bif{p(a)}{\cons(a,\filter(p,x))}{\filter(p,x)},\cons(a,x)) \\
 & = & \sublist(\cons(a,\filter(p,x)),\cons(a,x)) \\
 & = & \sublist(\filter(p,x),x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, note that $$\sublist(\filter(p,x),x) = \btrue,$$ so that
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,\cons(a,x)),\cons(a,x)) \\
 & = & \sublist(\bif{p(a)}{\cons(a,\filter(p,x))}{\filter(p,x)},\cons(a,x)) \\
 & = & \sublist(\filter(p,x),\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_filter :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_sublist_filter _ =
>   testName "sublist(filter(p)(x),x)" $
>   \p x -> sublist (filter p x) x

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ interacts conditionally with $\any$ and $\all$.

:::::: theorem :::::
Let $A$ be a set, let $x,y \in \lists{A}$, and let $p : A \rightarrow \bool$. If $\sublist(x,y) = \btrue$, then we have the following.

1. If $\all(p,y) = \btrue$ then $\all(p,x) = \btrue$.
2. If $\any(p,x) = \btrue$ then $\any(p,y) = \btrue$.

::: proof ::::::::::
1. We proceed by list induction on $y$. For the base case $y = \nil$, since $\sublist(x,y) = \btrue$ we have $x = \nil$. Now $$\all(p,y) = \all(p,\nil) = \btrue$$ and $$\all(p,x) = \all(p,\nil) = \btrue$$ as needed. For the inductive step, suppose the result holds for all $x$ for some $y$, and let $b \in A$. Suppose $\sublist(x,\cons(b,y)) = \btrue$, and further suppose that $\all(p,\cons(b,y)) = \btrue$. In particular, note that $p(b) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, note that $$\all(p,x) = \all(p,\nil) = \btrue,$$ so the implication holds regardless of $y$. Suppose instead that $x = \cons(a,u)$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \bif{\beq(a,b)}{\sublist(u,y)}{\sublist(\cons(a,u),y)} \\
 & = & \bif{\beq(a,b)}{\all(p,u)}{\all(p,\cons(a,u))} \\
 & = & \bif{\beq(a,b)}{\all(p,\cons(a,u))}{\all(p,\cons(a,u))} \\
 &     \href{@booleans@#thm-if-same}
   = & \all(p,\cons(a,u)) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as needed.
2. We prove this implication by contraposition. Suppose $\any(p,y) = \bfalse$; then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 &     \href{@not@#thm-not-false}
   = & \bnot(\bfalse) \\
 & = & \bnot(\any(p,y)) \\
 & = & \all(\bnot \circ p, y).
\end{eqnarray*}$$
Using (1), we thus have
$$\begin{eqnarray*}
 &   & \bfalse \\
 &     \href{@not@#thm-not-true}
   = & \bnot(\btrue) \\
 & = & \bnot(\all(\bnot \circ p,x)) \\
 & = & \bnot(\bnot(\any(p,x))) \\
 &     \href{@not@#thm-not-involution}
   = & \any(p,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_all :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_sublist_all _ =
>   testName "if sublist(x,y) then if all(p)(y) then all(p)(x)" $
>   \p x y -> if sublist x y
>     then if all p y then all p x else true
>     else true
> 
> 
> _test_sublist_any :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_sublist_any _ =
>   testName "if sublist(x,y) then if any(p)(x) then any(p)(y)" $
>   \p x y -> if sublist x y
>     then if any p x then any p y else true
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ is destroyed by $\cons$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. If $\sublist(x,y)$, then $\sublist(\cons(a,y),x) = \bfalse$.

::: proof ::::::::::
Suppose to the contrary that $\sublist(\cons(a,y),x) = \btrue$. By transitivity we have $\sublist(\cons(a,y),y)$, and we also have $\sublist(y,\cons(a,y))$, so by antisymmetry we have $y = \cons(a,y)$ -- a contradiction.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_cons_not :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> t a -> Bool)
> _test_sublist_cons_not _ =
>   testName "if sublist(x,y) then eq(sublist(cons(a,y),x),false)" $
>   \p a x y -> if sublist x y
>     then eq (sublist (cons a y) x) false
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\sublist$ on singleton lists is equivalent to $\elt$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have $$\sublist(\cons(a,\nil),x) = \elt(a,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,\nil),\nil) \\
 & = & \isnil(\cons(a,\nil)) \\
 & = & \bfalse \\
 & = & \elt(a,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,\nil),\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\sublist(\nil,x)}{\sublist(\cons(a,\nil),x)} \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,x)} \\
 & = & \elt(a,\cons(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublist_singleton_elt :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_sublist_singleton_elt _ =
>   testName "sublist(cons(a,nil),x) == elt(a,x)" $
>   \a x -> eq
>     (sublist (cons a nil) x)
>     (elt a x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_sublist ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a))
>   , Natural n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_sublist t n maxSize numCases = do
>   testLabel1 "sublist" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_sublist_list_nil t)
>   runTest args (_test_sublist_nil_cons t)
>   runTest args (_test_sublist_cons_cons t)
>   runTest args (_test_sublist_reflexive t)
>   runTest args (_test_sublist_nil_snoc t)
>   runTest args (_test_sublist_snoc_cancel t)
>   runTest args (_test_sublist_cat_left_cancel t)
>   runTest args (_test_sublist_cat_right_cancel t)
>   runTest args (_test_sublist_cons_right t)
>   runTest args (_test_sublist_cons_left t)
>   runTest args (_test_sublist_length t n)
>   runTest args (_test_sublist_antisymmetric t)
>   runTest args (_test_sublist_transitive t)
>   runTest args (_test_sublist_cat_compatible t)
>   runTest args (_test_sublist_snoc_snoc t)
>   runTest args (_test_sublist_rev t)
>   runTest args (_test_sublist_snoc_right t)
>   runTest args (_test_sublist_snoc_left t)
>   runTest args (_test_sublist_left_cat_right t)
>   runTest args (_test_sublist_right_cat_right t)
>   runTest args (_test_sublist_left_cat_left t)
>   runTest args (_test_sublist_right_cat_left t)
>   runTest args (_test_sublist_filter t)
>   runTest args (_test_sublist_all t)
>   runTest args (_test_sublist_any t)
>   runTest args (_test_sublist_cons_not t)
>   runTest args (_test_sublist_singleton_elt t)

Main:

> main_sublist :: IO ()
> main_sublist = do
>   _test_sublist (nil :: ConsList Bool)  (zero :: Unary) 50 200
>   _test_sublist (nil :: ConsList Unary) (zero :: Unary) 50 200
