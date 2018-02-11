---
title: Longest Common Prefix
author: nbloomf
date: 2017-05-09
tags: arithmetic-made-difficult, literate-haskell
slug: lcp-lcs
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module LongestCommonPrefix
>   ( lcp, lcs, _test_lcp, main_lcp
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
> import Lists
> import DoubleFold
> import Snoc
> import Reverse
> import Cat
> import Map
> import Zip
> import PrefixAndSuffix

Today we'll compute the *longest common prefix* of two lists (and while we're at it, the *longest common suffix*). Given two lists $x$ and $y$, their longest common prefix is the longest list which is a prefix of both, just like it says on the tin. We'll denote this function $\lcp$, and we want it to have a signature like $$\lists{A} \times \lists{A} \rightarrow \lists{A}.$$ Double fold was made for situations like this.

:::::: definition ::
Let $A$ be a set. Define $\delta : \lists{A} \rightarrow \lists{A}$ by $\delta(y) = \nil$, $\psi : A \times \lists{A} \rightarrow \lists{A}$ by $$\psi(a,x) = \nil,$$ and $\chi : A \times A \times \lists{A} \times \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\chi(a,b,y,z,w) = \bif{\beq(a,b)}{cons(a,z)}{\nil}.$$ Now define $\lcp : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\lcp = \dfoldr{\delta}{\psi}{\chi}.$$

In Haskell:

> lcp :: (List t, Equal a) => t a -> t a -> t a
> lcp = dfoldr delta psi chi
>   where
>     delta _ = nil
>     psi _ _ = nil
>     chi a b _ z _ = if eq a b then cons a z else nil

::::::::::::::::::::

Since $\lcp$ is defined as a double fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\lcp$ is the unique map $f : \lists{A} \times \lists{A} \rightarrow \lists{A}$ satisfying the following equations for all $a,b \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil,y) = \nil \\
 f(\cons(a,x),\nil) = \nil \\
 f(\cons(a,x),\cons(b,y)) = \bif{\beq(a,b)}{\cons(a,f(x,y))}{\nil}
\end{array}\right.$$

::: test :::::::::::

> _test_lcp_nil_list :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcp_nil_list _ =
>   testName "lcp(nil,y) == nil" $
>   \y -> eq (lcp nil y) nil
> 
> 
> _test_lcp_cons_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_lcp_cons_nil _ =
>   testName "lcp(cons(a,x),nil) == nil" $
>   \a x -> eq (lcp (cons a x) nil) nil
> 
> 
> _test_lcp_cons_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> a -> t a -> Bool)
> _test_lcp_cons_cons _ =
>   testName "lcp(cons(a,x),cons(b,y)) == if(eq(a,b),cons(a,lcp(x,y),nil))" $
>   \a x b y -> eq
>     (lcp (cons a x) (cons b y))
>     (if eq a b then cons a (lcp x y) else nil)

::::::::::::::::::::
::::::::::::::::::::

Now $\lcp$ lives up to the name (the *universal property* of $\lcp$):

:::::: theorem :::::
Let $A$ be a set. The following hold for all $x,y,z \in \lists{A}$.

1. $\prefix(\lcp(x,y),x)$ and $\prefix(\lcp(x,y),y)$.
2. If $\prefix(z,x)$ and $\prefix(z,y)$, then $\prefix(z,\lcp(x,y))$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(x,y),x) \\
 & = & \prefix(\lcp(\nil,y),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(x,y),y) \\
 & = & \prefix(\lcp(\nil,y),y) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equalities hold for all $y$ for some $x$, and let $a \in A$. We consider two cases for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\nil),\cons(a,x)) \\
 & = & \prefix(\nil,\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose now that $y = \cons(b,w)$. If $b = a$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(a,w)),\cons(a,x)) \\
 & = & \prefix(\cons(a,\lcp(x,w)),\cons(a,x)) \\
 & = & \prefix(\lcp(x,w),x) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(b,w)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(a,w)),\cons(a,w)) \\
 & = & \prefix(\cons(a,\lcp(x,w)),\cons(a,w)) \\
 & = & \prefix(\lcp(x,w),w) \\
 & = & \btrue,
\end{eqnarray*}$$
while if $b \neq a$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(a,x)) \\
 & = & \prefix(\nil,\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(b,w)) \\
 & = & \prefix(\nil,\cons(b,w)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $z$. For the base case $z = \nil$, note that $\prefix(\nil,x)$, $\prefix(\nil,y)$, and $\prefix(\nil,\lcp(x,y))$ are all $\btrue$. For the inductive step, suppose the result holds for all $x$ and $y$ for some $z$ and let $a \in A$. Suppose further that $\prefix(\cons(a,z),x)$ and $\prefix(\cons(a,z),y)$. Then we must have $x = \cons(a,u)$ and $y = \cons(a,v)$, and thus $\prefix(z,u)$ and $\prefix(z,v)$ are both $\btrue$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,z),\lcp(x,y)) \\
 & = & \prefix(\cons(a,z),\lcp(\cons(a,u),\cons(a,v))) \\
 & = & \prefix(\cons(a,z),\cons(a,\lcp(u,v))) \\
 & = & \prefix(z,\lcp(u,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_is_common :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_is_common _ =
>   testName "and(prefix(lcp(x,y),x),prefix(lcp(x,y),y))" $
>   \x y -> and (prefix (lcp x y) x) (prefix (lcp x y) y)
> 
> 
> _test_lcp_is_longest :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcp_is_longest _ =
>   testName "if and(prefix(z,x),prefix(z,y)) then prefix(z,lcp(x,y))" $
>   \x y z -> if and (prefix z x) (prefix z y)
>     then prefix z (lcp x y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\lcp$ is idempotent.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ we have $\lcp(x,x) = x$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(x,x) \\
 & = & \lcp(\nil,\nil) \\
 & = & \nil \\
 & = & x
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),\cons(a,x)) \\
 & = & \cons(a,\lcp(x,x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcp_idempotent _ =
>   testName "lcp(x,x) == x" $
>   \x -> eq (lcp x x) x

::::::::::::::::::::
::::::::::::::::::::

$\lcp$ is commutative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $\lcp(x,y) = \lcp(y,x)$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(x,y) \\
 & = & \lcp(\nil,y) \\
 & = & \nil \\
 & = & \lcp(y,\nil) \\
 & = & \lcp(y,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$, and let $a \in A$. Now we consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),y) \\
 & = & \lcp(\cons(a,x),\nil) \\
 & = & \nil \\
 & = & \lcp(\nil,\cons(a,x)) \\
 & = & \lcp(y,\cons(a,x))
\end{eqnarray*}$$
as needed. Now suppose $y = \cons(b,w)$. Then we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),y) \\
 & = & \lcp(\cons(a,x),\cons(b,w)) \\
 & = & \bif{\beq(a,b)}{\lcp(x,w)}{\nil} \\
 & = & \bif{\beq(b,a)}{\lcp(w,x)}{\nil} \\
 & = & \lcp(\cons(b,w),\cons(a,x)) \\
 & = & \lcp(y,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_commutative _ =
>   testName "lcp(x,y) == lcp(y,x)" $
>   \x y -> eq (lcp x y) (lcp y x)

::::::::::::::::::::
::::::::::::::::::::

$\lcp$ is associative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $\lcp(\lcp(x,y),z) = \lcp(x,\lcp(y,z))$.

::: proof ::::::::::
Let $h = \lcp(\lcp(x,y),z)$, $k = \lcp(x,\lcp(y,z))$, $u = \lcp(x,y)$, and $v = \lcp(y,z)$. First we show that $\prefix(h,k)$. Note that $\prefix(h,u)$, so that $\prefix(h,x)$ and $\prefix(h,y)$. Now $\prefix(h,z)$, so that $\prefix(h,v)$. Thus $\prefix(h,k)$. The proof that $\prefix(k,h)$ is similar; thus $h = k$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_associative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcp_associative _ =
>   testName "lcp(lcp(x,y),z) == lcp(x,lcp(y,z))" $
>   \x y z -> eq (lcp (lcp x y) z) (lcp x (lcp y z))

::::::::::::::::::::
::::::::::::::::::::

$\cat$ distributes over $\lcp$ from the left.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $\cat(x,\lcp(y,z)) = \lcp(\cat(x,y),\cat(x,z))$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \cat(x,\lcp(y,z)) \\
 & = & \cat(\nil,\lcp(y,z)) \\
 &     \href{@cat@#cor-cat-nil}
   = & \lcp(y,z) \\
 & = & \lcp(\cat(\nil,y),\cat(\nil,z)) \\
 & = & \lcp(\cat(x,y),\cat(x,z))
\end{eqnarray*}$$
as needed. Suppose now that the equality holds for all $y$ and $z$ for some $x$, and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \cat(\cons(a,x),\lcp(y,z)) \\
 &     \href{@cat@#cor-cat-cons}
   = & \cons(a,\cat(x,\lcp(y,z))) \\
 & = & \cons(a,\lcp(\cat(x,y),\cat(x,z))) \\
 & = & \lcp(\cons(a,\cat(x,y)),\cons(a,\cat(x,z))) \\
 & = & \lcp(\cat(\cons(a,x),y),\cat(\cons(a,x),z))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcp_cat_left _ =
>   testName "cat(x,lcp(y,z)) == lcp(cat(x,y),cat(x,z))" $
>   \x y z -> eq (cat x (lcp y z)) (lcp (cat x y) (cat x z))

::::::::::::::::::::
::::::::::::::::::::

$\lcp$ detects prefixes.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. Then $\lcp(x,y) = x$ if and only if $\prefix(x,y) = \btrue$.

::: proof ::::::::::
To see the "if" part, suppose $\prefix(x,y)$. Then we have $y = \cat(x,z)$ for some $z$. Now
$$\begin{eqnarray*}
 &   & \lcp(x,y) \\
 & = & \lcp(\cat(x,\nil),\cat(x,z)) \\
 & = & \cat(x,\lcp(\nil,z)) \\
 & = & \cat(x,\nil) \\
 &     \href{@cat@#thm-cat-nil-right}
   = & x
\end{eqnarray*}$$
as claimed. To see the "only if" part, suppose we have $\lcp(x,y) = x$; using the universal property of $\lcp$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,y) \\
 & = & \prefix(\lcp(x,y),y) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_prefix _ =
>   testName "lcp(x,y) == x iff prefix(x,y)" $
>   \x y -> eq (eq (lcp x y) x) (prefix x y)

::::::::::::::::::::
::::::::::::::::::::

And $\lcp$ interacts with $\zip$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $x,y \in \lists{A}$ and $u,v \in \lists{B}$. Then $$\lcp(\zip(x,u),\zip(y,v)) = \zip(\lcp(x,y),\lcp(u,v)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(x,u),\zip(y,v)) \\
 & = & \lcp(\zip(\nil,u),\zip(y,v)) \\
 & = & \lcp(\nil,\zip(y,v)) \\
 & = & \nil \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \zip(\lcp(\nil,y),\lcp(u,v)) \\
 & = & \zip(\lcp(x,y),\lcp(u,v))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(\nil,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\nil) \\
 & = & \nil \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),\nil),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v))
\end{eqnarray*}$$
as claimed. If $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),\nil),\zip(y,v)) \\
 & = & \lcp(\nil,\zip(y,v)) \\
 & = & \nil \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(\nil,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed. If $v = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,\nil)) \\
 & = & \lcp(\zip(\cons(a,x),u),\nil) \\
 & = & \nil \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,\nil)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed. Thus we can say $y = \cons(c,w)$, $u = \cons(b,h)$, and $v = \cons(d,k)$. If $a \neq c$, we have
$$\begin{eqnarray*}
 &   & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),\cons(c,w)),\lcp(u,v)) \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \nil \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,h)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
\end{eqnarray*}$$
as claimed. If $b \neq d$, we have
$$\begin{eqnarray*}
 &   & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(\cons(c,h),\cons(d,k))) \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \nil \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,h)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
\end{eqnarray*}$$
as claimed. Finally, suppose $a = c$ and $b = d$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),y),\zip(u,v)) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,w)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((a,b),\zip(w,k))) \\
 & = & \cons((a,b),\lcp(\zip(x,h),\zip(w,k))) \\
 & = & \cons((a,b),\zip(\lcp(x,w),\lcp(h,k))) \\
 & = & \zip(\cons(a,\lcp(x,w)),\cons(b,\lcp(h,k))) \\
 & = & \zip(\lcp(\cons(a,x),\cons(a,w)),\lcp(\cons(b,h),\cons(b,k))) \\
 & = & \zip(\lcp(\cons(a,x),\cons(c,w)),\lcp(\cons(b,h),\cons(d,k))) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_zip :: (List t, Equal a, Equal (t (Pair a a)))
>   => t a -> Test (t a -> t a -> t a -> t a -> Bool)
> _test_lcp_zip _ =
>   testName "zip(lcp(x,y),lcp(u,v)) == lcp(zip(x,u),zip(y,v))" $
>   \x y u v -> eq (zip (lcp x y) (lcp u v)) (lcp (zip x u) (zip y v))

::::::::::::::::::::
::::::::::::::::::::

$\lcp$ interacts with $\map(f)$ if $f$ is injective.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ an injective map. For all $x,y \in \lists{A}$ we have $$\map(f)(\lcp(x,y)) = \lcp(\map(f)(x),\map(f)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(x,y)) \\
 & = & \map(f)(\lcp(\nil,y)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \lcp(\nil,\map(f)(y)) \\
 & = & \lcp(\map(f)(\nil),\map(f)(y)) \\
 & = & \lcp(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as needed. Suppose now the equality holds for some $x$ and let $a \in A$. We consider two possitiblities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\nil)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \lcp(\map(f)(\cons(a,x)),\nil) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\nil)) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed. Suppose then that $y = \cons(b,u)$. If $a = b$, we have $f(a) = f(b)$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(a,u))) \\
 & = & \map(f)(\cons(a,\lcp(x,u))) \\
 & = & \cons(f(a),\map(f)(\lcp(x,u))) \\
 & = & \cons(f(a),\lcp(\map(f)(x),\map(f)(u))) \\
 & = & \lcp(\cons(f(a),\map(f)(x)),\cons(f(a),\map(f)(u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(a,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(b,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed. On the other hand, if $a \neq b$, then (since $f$ is injective) $f(a) \neq f(b)$. Then we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \map(f)(\lcp(x,u)) \\
 & = & \lcp(\map(f)(x),\map(f)(u)) \\
 & = & \lcp(\cons(f(a),\map(f)(x)),\cons(f(b),\map(f)(u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(b,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

And $\lcp$ interacts with $\map(f)$ and $\map(g)$ if $f$ and $g$ have no images in common.

:::::: theorem :::::
Let $A$ and $B$ be sets

1. Suppose $f,g : A \rightarrow B$ are functions with the property that $f(a) \neq g(b)$ for all $a,b \in A$. Then $\lcp(\map(f)(x),\map(g)(y)) = \nil$ for all $x,y \in \lists{A}$.
2. In particular, $f(x) = \cons(a,x)$ and $g(x) = \cons(b,x)$ have this property if $a \neq b$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \lcp(\map(f)(\nil),\map(g)(y)) \\
 & = & \lcp(\nil,\map(g)(y)) \\
 & = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$, and let $a \in A$. We have two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\map(f)(\cons(a,x)),\map(g)(\nil)) \\
 & = & \lcp(\map(f)(\cons(a,x)),\nil) \\
 & = & \nil
\end{eqnarray*}$$
as needed, and if $y = \cons(b,u)$, since $f(a) \neq g(b)$, we have
$$\begin{eqnarray*}
 &   & \lcp(\map(f)(\cons(a,x)),\map(g)(\cons(b,u))) \\
 & = & \lcp(\cons(f(a),\map(f)(x)),\cons(g(b))(\map(g)(u))) \\
 & = & \nil
\end{eqnarray*}$$
as needed.
2. Note that if $\cons(a,x) = \cons(b,y)$, we must have $a = b$.
::::::::::::::::::::

::: test :::::::::::

> _test_lcp_map_cons :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> Test (a -> a -> t (t a) -> t (t a) -> Bool)
> _test_lcp_map_cons _ =
>   testName "if a /= b then lcp(map(cons(a,-))(x),map(cons(b,-))(y)) == nil" $
>   \a b x y -> if not (eq a b)
>     then eq (lcp (map (cons a) x) (map (cons b) y)) nil
>     else true

::::::::::::::::::::
::::::::::::::::::::

We can define the dual operation, longest common suffix, in terms of $\lcp$ like so.

:::::: definition ::
Let $A$ be a set. We define $\lcs : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\lcs(x,y) = \rev(\lcp(\rev(x),\rev(y))).$$

In Haskell:

> lcs :: (List t, Equal a) => t a -> t a -> t a
> lcs x y = rev (lcp (rev x) (rev y))

::::::::::::::::::::

Many properties of $\lcp$ have analogues for $\lcs$.

:::::: corollary :::
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$, we have the following.

1. $\lcs(\nil,y) = \nil$.
2. $\lcs(\snoc(a,x),\nil) = \nil$.
3. $\lcs(\snoc(a,x),\snoc(b,y)) = \bif{\beq(a,b)}{\snoc(a,\lcs(x,y))}{\nil}$.

::: test :::::::::::

> _test_lcs_nil_list :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcs_nil_list _ =
>   testName "lcs(nil,y) == nil" $
>   \y -> eq (lcs nil y) nil
> 
> 
> _test_lcs_snoc_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_lcs_snoc_nil _ =
>   testName "lcs(snoc(a,x),nil) == nil" $
>   \a x -> eq (lcs (snoc a x) nil) nil
> 
> 
> _test_lcs_snoc_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> a -> t a -> Bool)
> _test_lcs_snoc_snoc _ =
>   testName "lcs(snoc(a,x),snoc(b,y)) == if(eq(a,b),snoc(a,lcs(x,y)),nil)" $
>   \a x b y -> eq
>     (lcs (snoc a x) (snoc b y))
>     (if eq a b then snoc a (lcs x y) else nil)

::::::::::::::::::::
::::::::::::::::::::

$\lcs$ lives up to the name.

:::::: theorem :::::
Let $A$ be a set with $x,y,z \in \lists{A}$. Then we have the following.

1. $\suffix(\lcs(x,y),x)$ and $\suffix(\lcs(x,y),y)$.
2. If $\suffix(z,x)$ and $\suffix(z,y)$, then $\suffix(z,\lcs(x,y))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \suffix(\lcs(x,y),x) \\
 & = & \prefix(\rev(\lcs(x,y)),\rev(x)) \\
 & = & \prefix(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(x)) \\
 & = & \prefix(\lcp(\rev(x),\rev(y)),\rev(x)) \\
 & = & \btrue,
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \suffix(\lcs(x,y),y) \\
 & = & \prefix(\rev(\lcs(x,y)),\rev(y)) \\
 & = & \prefix(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(y)) \\
 & = & \prefix(\lcp(\rev(x),\rev(y)),\rev(y)) \\
 & = & \btrue,
\end{eqnarray*}$$
2. Suppose $\suffix(z,x)$ and $\suffix(z,y)$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \suffix(z,x) \\
 & = & \prefix(\rev(z),\rev(x))
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \suffix(z,y) \\
 & = & \prefix(\rev(z),\rev(y)).
\end{eqnarray*}$$
So we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\rev(z),\lcp(\rev(x),\rev(y))) \\
 & = & \prefix(\rev(z),\rev(\rev(\lcp(\rev(x),\rev(y))))) \\
 & = & \prefix(\rev(z),\rev(\lcs(x,y))) \\
 & = & \suffix(z,\lcs(x,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_is_common :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcs_is_common _ =
>   testName "and(suffix(lcs(x,y),x),suffix(lcs(x,y),y))" $
>   \x y -> and (suffix (lcs x y) x) (suffix (lcs x y) y)
> 
> 
> _test_lcs_is_longest :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcs_is_longest _ =
>   testName "if and(suffix(z,x),suffix(z,y)) then suffix(z,lcs(x,y))" $
>   \x y z -> if and (suffix z x) (suffix z y)
>     then suffix z (lcs x y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\lcs$ is idempotent.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ we have $\lcs(x,x) = x$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \lcs(x,x) \\
 & = & \rev(\lcp(\rev(x),\rev(x))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcs_idempotent _ =
>   testName "lcs(x,x) == x" $
>   \x -> eq (lcs x x) x

::::::::::::::::::::
::::::::::::::::::::

$\lcs$ is commutative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $\lcs(x,y) = \lcs(y,x)$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \lcs(x,y) \\
 & = & \rev(\lcp(\rev(x),\rev(y))) \\
 & = & \rev(\lcp(\rev(y),\rev(x))) \\
 & = & \lcs(y,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcs_commutative _ =
>   testName "lcs(x,y) == lcs(y,x)" $
>   \x y -> eq (lcs x y) (lcs y x)

::::::::::::::::::::
::::::::::::::::::::

$\lcs$ is associative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $\lcs(\lcs(x,y),z) = \lcs(x,\lcs(y,z))$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \lcs(\lcs(x,y),z) \\
 & = & \lcs(\rev(\lcp(\rev(x),\rev(y))),z) \\
 & = & \rev(\lcp(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(z))) \\
 & = & \rev(\lcp(\lcp(\rev(x),\rev(y)),\rev(z))) \\
 & = & \rev(\lcp(\rev(x),\lcp(\rev(y),\rev(z)))) \\
 & = & \rev(\lcp(\rev(x),\rev(\rev(\lcp(\rev(y),\rev(z)))))) \\
 & = & \rev(\lcp(\rev(x),\rev(\lcs(y,z)))) \\
 & = & \lcs(x,\lcs(y,z))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_associative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcs_associative _ =
>   testName "lcs(lcs(x,y),z) == lcs(x,lcs(y,z))" $
>   \x y z -> eq (lcs (lcs x y) z) (lcs x (lcs y z))

::::::::::::::::::::
::::::::::::::::::::

$\cat$ distributes over $\lcs$ from the right.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have $\cat(\lcs(x,y),z) = \lcs(\cat(x,z),\cat(y,z))$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \lcs(\cat(x,z),\cat(y,z)) \\
 & = & \rev(\lcp(\rev(\cat(x,z)),\rev(\cat(y,z)))) \\
 & = & \rev(\lcp(\cat(\rev(z),\rev(x)),\cat(\rev(z),\rev(y)))) \\
 & = & \rev(\cat(\rev(z),\lcp(\rev(x),\rev(y)))) \\
 &     \href{@cat@#thm-rev-cat-antidistribute}
   = & \cat(\rev(\lcp(\rev(x),\rev(y))),\rev(\rev(z))) \\
 & = & \cat(\lcs(x,y),z)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcs_cat_right _ =
>   testName "cat(lcs(x,y),z) == lcs(cat(x,z),cat(y,z))" $
>   \x y z -> eq (cat (lcs x y) z) (lcs (cat x z) (cat y z))

::::::::::::::::::::
::::::::::::::::::::

$\lcs$ detects suffixes.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. Then $\lcs(x,y) = x$ if and only if $\suffix(x,y)$.

::: proof ::::::::::
Note that $$\lcs(x,y) = x$$ if and only if $$\rev(\lcp(\rev(x),\rev(y))) = x$$ if and only if $$\rev(\rev(\lcp(\rev(x),\rev(y)))) = \rev(x)$$ if and only if $$\lcp(\rev(x),\rev(y)) = \rev(x)$$ if and only if $$\prefix(\rev(x),\rev(y)) = \btrue$$ if and only if $$\suffix(x,y) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_lcs_suffix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcs_suffix _ =
>   testName "lcs(x,y) == x <==> suffix(x,y)" $
>   \x y -> eq (eq (lcs x y) x) (suffix x y)

::::::::::::::::::::
::::::::::::::::::::

And $\lcs$ also interacts with $\map(f)$ if $f$ is injective.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ an injective map. For all $x,y \in \lists{A}$ we have $$\map(f)(\lcs(x,y)) = \lcs(\map(f)(x),\map(f)(y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \map(f)(\lcs(x,y)) \\
 & = & \map(f)(\rev(\lcp(\rev(x),\rev(y)))) \\
 & = & \rev(\map(f)(\lcp(\rev(x),\rev(y)))) \\
 & = & \rev(\lcp(\map(f)(\rev(x)),\map(f)(\rev(y)))) \\
 & = & \rev(\lcp(\rev(\map(f)(x)),\rev(\map(f)(y)))) \\
 & = & \lcs(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_lcp ::
>   ( TypeName a, Equal a, Show a, Arbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (Pair a a))
>   , Arbitrary (t (t a)), Show (t (t a)), Equal (t (t a))
>   ) => t a -> Int -> Int -> IO ()
> _test_lcp t maxSize numCases = do
>   testLabel1 "lcp & lcs" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_lcp_nil_list t)
>   runTest args (_test_lcp_cons_nil t)
>   runTest args (_test_lcp_cons_cons t)
>   runTest args (_test_lcp_is_common t)
>   runTest args (_test_lcp_is_longest t)
>   runTest args (_test_lcp_idempotent t)
>   runTest args (_test_lcp_commutative t)
>   runTest args (_test_lcp_associative t)
>   runTest args (_test_lcp_cat_left t)
>   runTest args (_test_lcp_prefix t)
>   runTest args (_test_lcp_zip t)
>   runTest args (_test_lcp_map_cons t)
> 
>   runTest args (_test_lcs_nil_list t)
>   runTest args (_test_lcs_snoc_nil t)
>   runTest args (_test_lcs_snoc_snoc t)
>   runTest args (_test_lcs_is_common t)
>   runTest args (_test_lcs_is_longest t)
>   runTest args (_test_lcs_idempotent t)
>   runTest args (_test_lcs_commutative t)
>   runTest args (_test_lcs_associative t)
>   runTest args (_test_lcs_cat_right t)
>   runTest args (_test_lcs_suffix t)

Main:

> main_lcp :: IO ()
> main_lcp = do
>   _test_lcp (nil :: ConsList Bool)  20 100
>   _test_lcp (nil :: ConsList Unary) 20 100
