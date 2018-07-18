---
title: At
author: nbloomf
date: 2017-04-28
tags: arithmetic-made-difficult, literate-haskell
slug: at
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module At
>   ( at, _test_at, main_at
>   ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import LessThanOrEqualTo
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Cat
> import Length

The $\head$ function attempts to extract the "first" item in a list; in this post we'll generalize to $\at$, which extracts the element at an arbitrary position in a list.

:::::: definition ::
Define $\beta : \nats \times \lists{A} \rightarrow \bool$ by $$\beta(k,x) = \isnil(x),$$ $\psi : \nats \times \lists{A} \rightarrow 1 + A$ by $$\psi(k,x) = \lft(\ast),$$ and $\omega : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\omega(k,x) = \tail(x).$$ We then define $\at : \lists{A} \times \nats \rightarrow \ast + A$ by $$\at(x,k) = \bailrec(\head)(\beta)(\psi)(\omega)(k,x).$$

In Haskell:

> at :: (Natural n, Equal n, List t) => t a -> n -> Union () a
> at x k = bailoutRec head beta psi omega k x
>   where
>     beta _ z = isNil z
>     psi _ _ = lft ()
>     omega _ z = tail z

::::::::::::::::::::

Since $\at$ is defined in terms of $\bailrec$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-at-zero}[]{#cor-at-next}
$\at$ is the unique map $f : \nats \times \lists{A} \rightarrow 1 + A$ such that the following hold for all $n \in \nats$, $a \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(x,\zero) = \head(x) \\
 f(x,\next(n)) = \bif{\isnil(x)}{\lft(\ast)}{f(\tail(x),n)}
\end{array}\right.$$

::: test :::::::::::

> _test_at_zero
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_at_zero _ k =
>   testName "at(x,zero) == head(x)" $
>   \x -> eq
>     (at x (zero `withTypeOf` k))
>     (head x)
> 
> 
> _test_at_next
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_at_next _ k =
>   testName "at(x,next(n)) == if(isNil(x),lft(*),at(tail(x),n))" $
>   \n x -> eq
>     (at x ((next n) `withTypeOf` k))
>     (if isNil x then lft () else at (tail x) n)

::::::::::::::::::::
::::::::::::::::::::

$\at$ interacts with $\cons$ and $\next$.

:::::: theorem :::::
[]{#thm-at-cons-next}
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have $$\at(\cons(a,x),\next(k)) = \at(x,k).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\next(k)) \\
 &     \href{@at@#cor-at-next}
   = & \bif{\isnil(\cons(a,x))}{\lft(\ast)}{\at(\tail(\cons(a,x)),k)} \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \bif{\bfalse}{\lft(\ast)}{\at(\tail(\cons(a,x)),k)} \\
 &     \href{@booleans@#cor-if-false}
   = & \at(\tail(\cons(a,x)),k) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \at(x,k)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_next_next_cons
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> a -> n -> Bool)
> _test_at_next_next_cons _ _ =
>   testName "at(cons(a,x),next(next(k))) == at(x,next(k))" $
>   \x a k -> eq (at (cons a x) (next k)) (at x k)

::::::::::::::::::::
::::::::::::::::::::

Let's trace some special cases.

:::::: theorem :::::
[]{#thm-at-nil}[]{#thm-at-cons-zero}[]{#thm-at-doubleton-one}
Let $A$ be a set. The following hold for all $a,b \in A$, $x \in \lists{A}$, and $k \in \nats$.

1. $\at(\nil,k) = \lft(\ast)$.
2. $\at(\cons(a,x),\zero) = \rgt(a)$.
3. $\at(\cons(a,\cons(b,x)),\next(\zero)) = \rgt(b)$.

::: proof ::::::::::
1. We consider two cases: $k = \zero$ and $k \neq \zero$. If $k = \zero$, we of course have
$$\begin{eqnarray*}
 &   & \at(\nil,\zero) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast)
\end{eqnarray*}$$
as claimed. If $k = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\next(m)) \\
 &     \href{@at@#cor-at-next}
   = & \bif{\isnil(\nil)}{\lft(\ast)}{\at(\tail(\nil),m)} \\
 &     \href{@head-tail@#thm-isnil-nil}
   = & \bif{\btrue}{\lft(\ast)}{\at(\tail(\nil),m)} \\
 &     \href{@booleans@#cor-if-true}
   = & \lft(\ast)
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\zero) \\
 &     \href{@at@#cor-at-zero}
   = & \head(\cons(a,x)) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \rgt(a)
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),\next(\zero)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\cons(b,x),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(b)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_nil :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> Bool)
> _test_at_nil t _ =
>   testName "at(nil,k) == lft(*)" $
>   \n -> eq
>     (at (nil `withTypeOf` t) n)
>     (lft ())
> 
> 
> _test_at_single :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_at_single _ k =
>   testName "at(cons(a,nil),next(0)) == rgt(a)" $
>   \a x -> eq
>     (at (cons a x) (zero `withTypeOf` k))
>     (rgt a)
> 
> 
> _test_at_double :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> a -> t a -> Bool)
> _test_at_double _ k =
>   testName "at(cons(a,cons(b,nil)),next(next(0))) == rgt(b)" $
>   \a b x -> eq
>     (at (cons a (cons b x)) (next (zero `withTypeOf` k)))
>     (rgt b)

::::::::::::::::::::
::::::::::::::::::::

$\at$ interacts with $\length$.

:::::: theorem :::::
[]{#thm-at-cons-length}[]{#thm-at-length}
Let $A$ be a set and let $z \in \lists{A}$.

1. $\at(\cons(a,x),\length(x)) = \head(\rev(\cons(a,x)))$.
2. $\at(x,\length(x)) = \lft(\ast)$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\nil),\length(\nil)) \\
 &     \href{@length@#cor-length-nil}
   = & \at(\cons(a,\nil),\zero) \\
 & = & \rgt(a) \\
 &     \href{@head-tail@#thm-head-cons}
   = & \head(\cons(a,\nil)) \\
 & = & \head(\rev(\cons(a,\nil)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),\length(\cons(b,x))) \\
 &     \href{@length@#cor-length-cons}
   = & \at(\cons(a,\cons(b,x)),\next(\length(x))) \\
 & = & \at(\cons(b,x),length(x)) \\
 & = & \head(\rev(\cons(b,x))) \\
 & = & \head(\snoc(a,\rev(\cons(b,x)))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \head(\rev(\cons(a,\cons(b,x))))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\length(\nil)) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\length(\cons(a,x))) \\
 &     \href{@length@#cor-length-cons}
   = & \at(\cons(a,x),\next(\length(x))) \\
 & = & \at(x,\length(x)) \\
 &     \href{@at@#thm-at-length}
   = & \lft(\ast)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_length
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_at_length _ k =
>   testName "at(cons(a,x),length(x)) == head(rev(cons(a,x)))" $
>   \a x -> eq
>     (at (cons a x) ((length x) `withTypeOf` k))
>     (head (rev (cons a x)))
> 
> 
> _test_at_next_length
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_at_next_length _ k =
>   testName "at(x,next(length(x))) == lft(*)" $
>   \x -> eq
>     (at x ((length x) `withTypeOf` k))
>     (lft ())

::::::::::::::::::::
::::::::::::::::::::

$\at$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. Let $a,b \in A$ and $x \in \lists{A}$.

1. If $\nleq(k,\length(x))$ then $\at(\snoc(a,\cons(b,x)),k) = \at(\cons(b,x),k)$.
2. $\at(\snoc(a,x),\length(x)) = \rgt(a)$.

::: proof ::::::::::
1. We proceed by induction on $k$. For the base case $k = \zero$, note that $\nleq(k,\length(x))$, and we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),\zero) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \at(\cons(b,\snoc(a,x)),\zero) \\
 & = & \rgt(b) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \at(\cons(b,x),\zero)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$, $a$, and $b$ for some $k$, and suppose further that $\nleq(\next(k),\length(x))$. In particular, we must have $x = \cons(c,u)$ for some $c \in A$ and $u \in \lists{A}$, and $\nleq(k,\length(u))$. Now we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),\next(k)) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \at(\cons(b,\snoc(a,x)),\next(k)) \\
 & = & \at(\snoc(a,x),k) \\
 & = & \at(\snoc(a,\cons(c,u)),k) \\
 & = & \at(\cons(c,u),k) \\
 & = & \at(x,k) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\cons(b,x),\next(k))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\nil),\length(\nil)) \\
 & = & \at(\cons(a,\nil),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),\length(\cons(b,x))) \\
 & = & \at(\cons(b,\snoc(a,x)),\next(\length(x))) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\snoc(a,x),\length(x)) \\
 & = & \rgt(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_snoc
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> a -> a -> n -> Bool)
> _test_at_snoc _ _ =
>   testName "if leq(k,length(x)) then at(snoc(a,cons(b,x)),k) == at(cons(b,x),k)" $
>   \x a b k -> if leq k (length x)
>     then eq (at (snoc a (cons b x)) k) (at (cons b x) k)
>     else true
> 
> 
> _test_at_snoc_length
>   :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> a -> Bool)
> _test_at_snoc_length _ k =
>   testName "at(snoc(a,x),length(x)) == rgt(a)" $
>   \x a -> eq (at (snoc a x) ((length x) `withTypeOf` k)) (rgt a)

::::::::::::::::::::
::::::::::::::::::::

$\at$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set. Let $x \in \lists{A}$ and $u,v \in \nats$. If $\next(\nplus(u,v)) = \length(x)$, then we have $$\at(\rev(x),v) = \at(x,u).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that $\length(x) = \zero$, so that $\next(\nplus(u,v)) = \length(x)$ is false for all $u$ and $v$, and thus the implication holds vacuously. For the inductive step, suppose the implication holds for all $u$ and $v$ for some $x$ and let $a \in A$. Suppose further that $\next(\nplus(u,v)) = \length(\cons(a,x))$. We have two possibilities for $u$. If $u = \zero$, we have $\next(v) = \length(\cons(a,x))$ and thus $v = \length(x)$. In this case, we have
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),u) \\
 & = & \at(\cons(a,x),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(a) \\
 & = & \at(\snoc(a,\rev(x)),\length(\rev(x))) \\
 &     \href{@length@#thm-length-rev}
   = & \at(\snoc(a,\rev(x)),\length(x)) \\
 &     \href{@rev@#cor-rev-cons}
   = & \at(\rev(\cons(a,x)),\length(x)) \\
 & = & \at(\rev(\cons(a,x)),v)
\end{eqnarray*}$$
as needed. If $u = \next(w)$, then we have $\next(\nplus(w,v)) = \length(x)$. In particular, we have $x \neq \nil$ and thus $\rev(x) \neq \nil$; say $\rev(x) = \cons(c,y)$. Now $\nleq(v,\length(y))$, and moreover
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),u) \\
 & = & \at(\cons(a,x),\next(w)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(x,w) \\
 & = & \at(\rev(x),v) \\
 & = & \at(\cons(c,y),v) \\
 & = & \at(\snoc(a,\cons(c,y)),v) \\
 & = & \at(\snoc(a,\rev(x)),v) \\
 &     \href{@rev@#cor-rev-cons}
   = & \at(\rev(\cons(a,x)),v)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_rev :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> n -> n -> Bool)
> _test_at_rev _ _ =
>   testName "if eq(next(plus(u,v)),length(x)) then eq(at(x,u),at(rev(x),v))" $
>   \x u v -> if eq (next (plus u v)) (length x)
>     then eq (at x u) (at (rev x) v)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\at$ interacts with $\cat$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$, $x,y \in \lists{A}$ and $k \in \nats$, we have the following.

1. If $\nleq(k,\length(x))$, then $\at(\cat(\cons(a,x),y),k) = \at(\cons(a,x),k)$.
2. If $\at(\cat(\cons(a,x),y),\nplus(\next(\length(x)),k)) = \at(y,k)$.

::: proof ::::::::::
1. We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\cat(\cons(a,x),\nil),k) \\
 &     \href{@cat@#thm-cat-nil-right}
   = & \at(\cons(a,x),k)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the implication holds for all $k$, $a$, and $x$ for some $y$, and let $b \in A$, and suppose further that $\nleq(k,\length(x))$. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \at(\cat(\cons(a,x),\cons(b,y)),k) \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \at(\cat(\snoc(b,\cons(a,x)),y),k) \\
 & = & \at(\snoc(b,\cons(a,x)),k) \\
 & = & \at(\cons(a,x),k)
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\cat(\cons(a,\nil),y),\nplus(\next(\length(\nil)),k)) \\
 & = & \at(\cons(a,\cat(\nil,y)),\next(\nplus(\zero,k))) \\
 & = & \at(\cons(a,y),\next(k)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(y,k)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$, $y$, and $k$ for some $x$, and let $b \in A$. Note that $\snoc(b,x) = \cons(c,u)$ for some $c$ and u$, where $\length(x) = \next(\length(u))$. Now
$$\begin{eqnarray*}
 &   & \at(\cat(\cons(a,x),\cons(b,y)),\nplus(\next(\length(x)),k)) \\
 & = & \at(\cat(\snoc(b,\cons(a,x)),y),\next(\nplus(\length(x),k))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \at(\cat(\cons(a,\snoc(b,x)),y),\next(\nplus(\length(x),k))) \\
 & = & \at(\cons(a,\cat(\snoc(b,x)),y),\next(\nplus(\length(x),k))) \\
 & = & \at(\cat(\snoc(b,x),y),\nplus(\length(u),k)) \\
 & = & \at(\cat(\snoc(b,x),y),\nplus(\next(\length(u)),k)) \\
 & = & \at(\cat(\cons(c,u),y),\nplus(\next(\length(u)),k)) \\
 & = & \at(\cons(b,y),k)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_cat_left :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> t a -> n -> Bool)
> _test_at_cat_left _ _ =
>   testName "if leq(k,length(x)) then eq(at(cat(cons(a,x),y),k),at(cons(a,x),k))" $
>   \a x y k -> if leq k (length x)
>     then eq (at (cat (cons a x) y) k) (at (cons a x) k)
>     else true
> 
> 
> _test_at_cat_right :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> t a -> n -> Bool)
> _test_at_cat_right _ _ =
>   testName "eq(at(cat(cons(a,x),y),plus(next(length(x)),k)),at(y,k))" $
>   \a x y k -> eq
>     (at (cat (cons a x) y) (plus (next (length x)) k))
>     (at y k)

::::::::::::::::::::
::::::::::::::::::::

We can characterize the $k$s such that $\at(x,k)$ is a $\lft$ or a $\rgt$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$ we have the following.

1. If $\nleq(\length(x),k)$, then $\at(x,k) = \lft(\ast)$.
2. If $\nleq(k,\length(x))$, then $\at(\cons(a,x),k) = \rgt(b)$ for some $b \in A$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, note that for any $k$ we have $\nleq(\zero,k)$ and
$$\begin{eqnarray*}
 &   & \at(\nil,k) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $k$ for some $x$ and let $a \in A$. Suppose further that $\nleq(\length(\cons(a,x),k))$; we then have $k = \next(m)$ for some $m$, where $\nleq(\length(x),m)$. Now
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),k) \\
 & = & \at(\cons(a,x),\next(m)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(x,m) \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that if $\nleq(k,\length(\nil))$ then $k = \zero$. Now
$$\begin{eqnarray*}
 &   & \at(\cons(a,\nil),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $k$ and $a$ for some $x$ and let $b \in A$. Suppose further that $\nleq(k,\length(\cons(b,x)))$. We have two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(a)
\end{eqnarray*}$$
as needed. Suppose instead that $k = \next(m)$. Now $\nleq(m,\length(x))$, and we have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),k) \\
 & = & \at(\cons(a,\cons(b,x)),\next(m)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\cons(b,x),m) \\
 & = & \rgt(c)
\end{eqnarray*}$$
for some $c$ by the inductive hypothesis, as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_isleft :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> n -> Bool)
> _test_at_isleft _ _ =
>   testName "if leq(length(x),k) then isLft(at(x,k))" $
>   \x k -> if leq (length x) k
>     then isLft (at x k)
>     else true
> 
> 
> _test_at_isright :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> n -> Bool)
> _test_at_isright _ _ =
>   testName "if leq(k,length(x)) then isRgt(at(cons(a,x),k))" $
>   \a x k -> if leq k (length x)
>     then isRgt (at (cons a x) k)
>     else true

::::::::::::::::::::
::::::::::::::::::::

Finally, $\at$ detects equality for lists.

:::::: theorem :::::
Let $A$ be a set, and let $x,y \in \lists{A}$. Then $x = y$ if and only if $\at(x,k) = \at(y,k)$ for all $k \in \nats$.

::: proof ::::::::::
The "only if" direction is clear. We show the "if" part by list induction on $x$. For the base case $x = \nil$, suppose we have $\at(x,k) = \at(y,k)$ for all $k \in \nats$. If $y = \cons(a,z)$ for some $z$, then we have
$$\begin{eqnarray*}
 &   & \rgt(a) \\
 & = & \at(\cons(a,z),\next(\zero)) \\
 & = & \at(y,\next(\zero)) \\
 & = & \at(x,\next(\zero)) \\
 & = & \lft(\ast),
\end{eqnarray*}$$
a contradiction. So $y = \nil = x$ as claimed.

For the inductive step, suppose the implication holds for all $y$ for some $x$, let $a \in A$, and suppose we have $\at(\cons(a,x),k) = \at(y,k)$ for all $k \in \nats$. If $y = \nil$, then again we have
$$\begin{eqnarray*}
 &   & \rgt(a) \\
 & = & \at(\cons(a,x),\next(\zero)) \\
 & = & \at(y,\next(\zero)) \\
 & = & \at(\nil,\next(\zero)) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast)
\end{eqnarray*}$$
a contradiction. Say $y = \cons(b,z)$. Now
$$\begin{eqnarray*}
 &   & \at(z,k) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\cons(b,z),\next(k)) \\
 & = & \at(y,\next(k)) \\
 & = & \at(\cons(a,x),\next(k)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(x,k)
\end{eqnarray*}$$
By the inductive hypothesis, $x = z$, so that $\cons(a,x) = y$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_at_eq :: (List t, Equal a, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> t a -> n -> Bool)
> _test_at_eq _ _ =
>   testName "if eq(x,y) then eq(at(x,k),at(y,k))" $
>   \x y k -> if eq x y
>     then eq (at x k) (at y k)
>     else true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_at ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t a), List t, Equal (t a), Show (t a), Arbitrary (t a)
>   ) => Int -> Int -> t a -> n -> IO ()
> _test_at size cases t n = do
>   testLabel2 "at" t n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_at_zero t n)
>   runTest args (_test_at_next t n)
>   runTest args (_test_at_next_next_cons t n)
>   runTest args (_test_at_nil t n)
>   runTest args (_test_at_single t n)
>   runTest args (_test_at_double t n)
>   runTest args (_test_at_length t n)
>   runTest args (_test_at_next_length t n)
>   runTest args (_test_at_snoc t n)
>   runTest args (_test_at_snoc_length t n)
>   runTest args (_test_at_rev t n)
>   runTest args (_test_at_cat_left t n)
>   runTest args (_test_at_cat_right t n)
>   runTest args (_test_at_isleft t n)
>   runTest args (_test_at_isright t n)
>   runTest args (_test_at_eq t n)

Main:

> main_at :: IO ()
> main_at = do
>   _test_at 20 100 (nil :: ConsList Bool)  (zero :: Unary)
>   _test_at 20 100 (nil :: ConsList Unary) (zero :: Unary)
