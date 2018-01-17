---
title: Prefix and Suffix
author: nbloomf
date: 2017-05-08
tags: arithmetic-made-difficult, literate-haskell
slug: prefix-suffix
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module PrefixAndSuffix
>   ( prefix, suffix, _test_prefix_suffix, main_prefix_suffix
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import LessThanOrEqualTo
> import Lists
> import DoubleFold
> import Snoc
> import Reverse
> import Cat
> import Length
> import Map
> import Zip

The $\cat$ function on $\lists{A}$ is analogous to $\nplus$ on $\nats$. Carrying this analogy further, $\zip$ and $\zipPad$ are analogous to $\nmin$ and $\nmax$, respectively. When analogies like this occur in mathematics it can be fruitful to see how far they go. With that in mind, today we will explore the list-analogue of $\nleq$. This role is played by two functions which we call $\prefix$ and $\suffix$.

Intuitively, $\prefix$ will detect when one list is an initial segment of another, while $\suffix$ detects when one list is a terminal segment of another. We'll start with $\prefix$, which we can define as a $\dfoldr{\ast}{\ast}{\ast}$ as follows.

:::::: definition ::
Let $A$ be a set. Define $\delta : \lists{A} \rightarrow \bool$ by $\delta(y) = \btrue$, define $\psi : A \times \bool \rightarrow \bool$ by $\psi(a,p) = \bfalse$, and define $\chi : A \times A \times \lists{A} \times \bool \times \bool \rightarrow \lists{A}$ by $$\chi(a,b,y,p,q) = \bif{\beq(a,b)}{p}{\bfalse}.$$ Now define $$\prefix : \lists{A} \times \lists{A} \rightarrow \bool$$ by $$\prefix = \dfoldr{\delta}{\psi}{\chi}.$$

In Haskell:

> prefix :: (List t, Equal a) => t a -> t a -> Bool
> prefix = dfoldr delta psi chi
>   where
>     delta _ = true
>     psi _ _ = false
>     chi a b _ p _ = if eq a b then p else false

::::::::::::::::::::

Since $\prefix$ is defined as a double fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\prefix$ is the unique map $f : \lists{A} \times \lists{A} \rightarrow \bool$ satisfying the following equations for all $a,b \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil,y) = \btrue \\
 f(\cons(a,x),\nil) = \bfalse \\
 f(\cons(a,x),\cons(b,y)) = \bif{\beq(a,b)}{f(x,y)}{\bfalse}
\end{array}\right.$$

::: test :::::::::::

> _test_prefix_nil_list :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_prefix_nil_list _ =
>   testName "prefix(nil,y) == true" $
>   \y -> eq (prefix nil y) true
> 
> 
> _test_prefix_cons_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_prefix_cons_nil _ =
>   testName "prefix(cons(a,x),nil) == false" $
>   \a x -> eq (prefix (cons a x) nil) false
> 
> 
> _test_prefix_cons_cons :: (List t, Equal a)
>   => t a -> Test (a -> t a -> a -> t a -> Bool)
> _test_prefix_cons_cons _ =
>   testName "prefix(cons(a,x),cons(b,y)) == if(eq(a,b),prefix(x,y),false)" $
>   \a x b y -> eq
>     (prefix (cons a x) (cons b y))
>     (if eq a b then prefix x y else false)

::::::::::::::::::::
::::::::::::::::::::

Now $\prefix$ is analogous to $\nleq$ in that it detects the existence of solutions $z$ to the equation $y = \cat(x,z)$.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $x,y \in \lists{A}$.

1. $\prefix(x,\cat(x,y)) = \btrue$.
2. If $\prefix(x,y) = \btrue$, then $y = \cat(x,z)$ for some $z \in \lists{A}$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, certainly we have
$$\begin{eqnarray*}
 &   & \prefix(x,\cat(x,y)) \\
 & = & \prefix(\nil,\cat(\nil,y)) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue.
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,x),\cat(\cons(a,x),y)) \\
 & = & \prefix(\cons(a,x),\cons(a,\cat(x,y))) \\
 & = & \prefix(x,\cat(x,y)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that $$\prefix(\nil,y) = \btrue,$$ and $$y = \cat(\nil,y).$$ For the inductive step, suppose the result holds for some $x$, and let $a \in A$. Now suppose $\prefix(\cons(a,x),y) = \btrue$; in particular, we must have $y = \cons(a,w)$ for some $w$, and $\prefix(x,w) = \btrue$. By the induction hypothesis we have $w = \cat(x,z)$ for some $z$, and thus
$$\begin{eqnarray*}
 &   & y \\
 & = & \cons(a,w) \\
 & = & \cons(a,\cat(x,z)) \\
 & = & \cat(\cons(a,x),z)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_cat :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> Bool)
> _test_prefix_cat _ =
>   testName "prefix(x,cat(x,y))" $
>   \x y -> prefix x (cat x y)

::::::::::::::::::::
::::::::::::::::::::

And $\prefix$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$, if $\prefix(x,y) = \btrue$, then $\prefix(x,\snoc(a,y)) = \btrue$.

::: proof ::::::::::
If $\prefix(x,y) = \btrue$, then $y = \cat(x,z)$ for some $z$. Now $$\snoc(a,y) = \snoc(\cat(x,z)) = \cat(x,\snoc(a,z)),$$ and so $\prefix(x,\snoc(a,y)) = \btrue$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_snoc :: (List t, Equal a)
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_prefix_snoc _ =
>   testName "if prefix(x,y) then prefix(x,snoc(a,y))" $
>   \a x y -> if prefix x y
>     then prefix x (snoc a y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\prefix$ is a partial order.

:::::: theorem :::::
Let $A$ be a set. Then we have the following for all $x,y,z \in \lists{A}$.

1. $\prefix(x,x) = \btrue$.
2. If $\prefix(x,y)$ and $\prefix(y,x)$, then $x = y$.
3. If $\prefix(x,y)$ and $\prefix(y,z)$, then $\prefix(x,z)$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(x,\cat(x,\nil)) \\
 & = & \prefix(x,x)
\end{eqnarray*}$$
as claimed.
2. If $\prefix(x,y)$, we have $y = \cat(x,u)$ for some $u$. Similarly, if $\prefix(y,x)$ then $x = \cat(y,v)$ for some $v. Now
$$\begin{eqnarray*}
 &   & \cat(x,\nil) \\
 & = & x \\
 & = & \cat(y,v) \\
 & = & \cat(\cat(x,u),v) \\
 & = & \cat(x,\cat(u,v)).
\end{eqnarray*}$$
Since $\cat$ is cancellative, we have $\nil = \cat(u,v)$, so that $u = \nil$, and thus $x = y$ as claimed.
3. If $\prefix(x,y)$, we have $y = \cat(x,u)$. Similarly, if $\prefix(y,z)$, we have $z = \cat(y,v)$. Now $$z = \cat(\cat(x,u),v) = \cat(x,\cat(u,v))$$ so that $\prefix(x,z)$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_reflexive :: (List t, Equal a)
>   => t a -> Test (t a -> Bool)
> _test_prefix_reflexive _ =
>   testName "prefix(x,x)" $
>   \x -> prefix x x
> 
> 
> _test_prefix_symmetric :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_prefix_symmetric _ =
>   testName "prefix(x,y) & prefix(y,x) ==> eq(x,y)" $
>   \x y -> if and (prefix x y) (prefix y x)
>     then eq x y
>     else true
> 
> 
> _test_prefix_transitive :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_prefix_transitive _ =
>   testName "prefix(x,y) & prefix(y,z) ==> prefix(x,z)" $
>   \x y z -> if and (prefix x y) (prefix y z)
>     then prefix x z
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\map$ preserves $\prefix$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$, and let $x,y \in \lists{A}$. If $\prefix(x,y) = \btrue$, then $$\prefix(\map(f)(x),\map(f)(y)) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,y) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\map(f)(x),\map(f)(y)) \\
 & = & \prefix(\map(f)(\nil),\map(f)(y)) \\
 & = & \prefix(\nil,\map(f)(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose now the implication holds for some $x$, and let $a \in A$. Suppose further that $\prefix(\cons(a,x),y)$. Now $y = \cons(a,w)$ for some $w$, and we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\cons(a,x),y) \\
 & = & \prefix(\cons(a,x),\cons(a,w)) \\
 & = & \prefix(x,w).
\end{eqnarray*}$$
Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\map(f)(\cons(a,x)),\map(f)(y)) \\
 & = & \prefix(\map(f)(\cons(a,x)),\map(f)(\cons(a,w))) \\
 & = & \prefix(\cons(f(a),\map(f)(x)),\cons(f(a),\map(f)(w))) \\
 & = & \prefix(\map(f)(x),\map(f)(w)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_map :: (List t, Equal a)
>   => t a -> Test ((a -> a) -> t a -> t a -> Bool)
> _test_prefix_map _ =
>   testName "if prefix(x,y) then prefix(map(f)(x),map(f)(y))" $
>   \f x y -> if prefix x y
>     then prefix (map f x) (map f y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

And $\zip$ preserves $\prefix$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $x,y \in \lists{A}$ and $u,v \in \lists{B}$. If $\prefix(x,y) = \btrue$ and $\prefix(u,v) = \btrue$, then $$\prefix(\zip(x,u),\zip(y,v)) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that $\prefix(x,y) = \btrue$. Suppose further that $\prefix(u,v) = \btrue$; now
$$\begin{eqnarray*}
 &   & \prefix(\zip(x,u),\zip(y,v)) \\
 & = & \prefix(\zip(\nil,u),\zip(y,v)) \\
 & = & \prefix(\nil,\zip(y,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. Suppose further that $\prefix(\cons(a,x),y)$ and $\prefix(u,v)$; in particular we must have $y = \cons(a,k)$ for some $k \in \lists{A}$ with $\prefix(x,k)$, as otherwise $\prefix(\cons(a,x),y) = \bfalse$. Now we have two possibilities for $u$. If $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \prefix(\zip(\cons(a,x),\nil),\zip(y,v)) \\
 & = & \prefix(\nil,\zip(y,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose then that $u = \cons(b,w)$. Again we must have $v = \cons(b,h)$ with $h \in \lists{B}$ and $\prefix(w,h)$, since otherwise we have $\prefix(u,v) = \bfalse$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \prefix(\zip(\cons(a,x),\cons(b,w)),\zip(\cons(a,k),\cons(b,h))) \\
 & = & \prefix(\cons((a,b),\zip(x,w)),\cons((a,b),\zip(k,h))) \\
 & = & \prefix(\zip(x,w),\zip(k,h)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_zip :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> t a -> t a -> Bool)
> _test_prefix_zip _ =
>   testName "prefix(x,y) & prefix(u,v) ==> prefix(zip(x,u),zip(y,v))" $
>   \x y u v -> if and (prefix x y) (prefix u v)
>     then prefix (zip x u) (zip y v)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\prefix$ interacts with $\length$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. If $\prefix(x,y)$, then $\nleq(\length(x),\length(y))$.

::: proof ::::::::::
Suppose $\prefix(x,y)$. Then we have $y = \cat(x,z)$ for some $z$, and so
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\length(x),\length(\cat(x,z))) \\
 & = & \nleq(\length(x),\nplus(\length(x),\length(z))) \\
 & = & \nleq(\zero,\length(z)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_length :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (t a -> t a -> Bool)
> _test_prefix_length _ k =
>   testName "if prefix(x,y) then leq(length(x),length(y))" $
>   \x y -> if prefix x y
>     then leq ((length x) `withTypeOf` k) (length y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

The simplest way to define $\suffix$ is in terms of $\prefix$.

:::::: definition ::
Let $A$ be a set. Define $\suffix : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\suffix(x,y) = \prefix(\rev(x),\rev(y)).$$

In Haskell:

> suffix :: (List t, Equal a) => t a -> t a -> Bool
> suffix x y = prefix (rev x) (rev y)

::::::::::::::::::::

Not surprisingly, we can characterize $\prefix$ in terms of $\suffix$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. Then $$\prefix(x,y) = \suffix(\rev(x),\rev(y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \suffix(\rev(x),\rev(y)) \\
 & = & \prefix(\rev(\rev(x)),\rev(\rev(y))) \\
 & = & \prefix(x,y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_suffix_prefix _ =
>   testName "prefix(x,y) == suffix(rev(x),rev(y))" $
>   \x y -> eq (prefix x y) (suffix (rev x) (rev y))

::::::::::::::::::::
::::::::::::::::::::

Many theorems about $\prefix$ has an analogue for $\suffix$.

:::::: theorem :::::
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$, we have the following.

1. $\suffix(\nil,y) = \btrue$.
2. $\suffix(\snoc(a,x),\nil) = \bfalse$.
3. $$\suffix(\snoc(a,x),\snoc(b,y)) = \left\{\begin{array}{ll} \bfalse & \mathrm{if}\ a \neq b \\ \suffix(x,y) & \mathrm{if}\ a = b. \end{array}\right.$$

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \suffix(\nil,y) \\
 & = & \prefix(\rev(\nil),\rev(y)) \\
 & = & \prefix(\nil,\rev(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\nil) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\nil)) \\
 & = & \prefix(\cons(a,\rev(x)),\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. First suppose $a = b$. Now
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\snoc(b,y)) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\snoc(b,y))) \\
 & = & \prefix(\cons(a,\rev(x)),\cons(b,\rev(y))) \\
 & = & \prefix(\rev(x),\rev(y)) \\
 & = & \suffix(x,y)
\end{eqnarray*}$$
as claimed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\snoc(b,y)) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\snoc(b,y))) \\
 & = & \prefix(\cons(a,\rev(x)),\cons(b,\rev(y))) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_nil_list :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_suffix_nil_list _ =
>   testName "suffix(nil,y) == true" $
>   \y -> eq (suffix nil y) true
> 
> 
> _test_suffix_snoc_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_suffix_snoc_nil _ =
>   testName "suffix(snoc(a,x),y) == true" $
>   \a x -> eq (suffix (snoc a x) nil) false
> 
> 
> _test_suffix_snoc_snoc :: (List t, Equal a)
>   => t a -> Test (a -> t a -> a -> t a -> Bool)
> _test_suffix_snoc_snoc _ =
>   testName "suffix(snoc(a,x),snoc(b,y)) == if(eq(a,b),suffix(x,y),false)" $
>   \a x b y -> eq
>     (suffix (snoc a x) (snoc b y))
>     (if eq a b then suffix x y else false)

::::::::::::::::::::
::::::::::::::::::::

$\suffix$ also detects the existence of solutions $z$ to the equation $y = \cat(z,x)$.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $x,y \in \lists{A}$.

1. $\suffix(x,\cat(y,x)) = \btrue$.
2. If $\suffix(x,y) = \btrue$, then $y = \cat(z,x)$ for some $z \in \lists{A}$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \suffix(x,\cat(y,x)) \\
 & = & \prefix(\rev(x),\rev(\cat(y,x))) \\
 & = & \prefix(\rev(x),\cat(\rev(x),\rev(y))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Suppose $\suffix(x,y) = \btrue$. Then $\prefix(\rev(x),\rev(y)) = \btrue$, so we have $\rev(y) = \cat(\rev(x),w)$ for some $w$. Now
$$\begin{eqnarray*}
 &   & y \\
 & = & \rev(\rev(y)) \\
 & = & \rev(\cat(\rev(x),w)) \\
 & = & \cat(\rev(w),\rev(\rev(x))) \\
 & = & \cat(\rev(w),x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_cat :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> Bool)
> _test_suffix_cat _ =
>   testName "suffix(x,cat(y,x))" $
>   \x y -> suffix x (cat y x)

::::::::::::::::::::
::::::::::::::::::::

$\suffix$ interacts with $\cons$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ and $a \in A$, if $\suffix(x,y)$, then $\suffix(x,\cons(a,y))$.

::: proof ::::::::::
Suppose $\suffix(x,y)$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \suffix(x,y) \\
 & = & \prefix(\rev(x),\rev(y)) \\
 & = & \prefix(\rev(x),\snoc(a,\rev(y))) \\
 & = & \prefix(\rev(x),\rev(\cons(a,y))) \\
 & = & \suffix(x,\cons(a,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_cons :: (List t, Equal a)
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_suffix_cons _ =
>   testName "if suffix(x,y) then suffix(x,cons(a,y))" $
>   \a x y -> if suffix x y
>     then suffix x (cons a y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\suffix$ is a partial order:

:::::: theorem :::::
Let $A$ be a set. Then we have the following for all $x,y,z \in \lists{A}$.

1. $\suffix(x,x) = \btrue$.
2. If $\suffix(x,y)$ and $\suffix(y,x)$, then $x = y$.
3. If $\suffix(x,y)$ and $\suffix(y,z)$, then $\suffix(x,z)$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\rev(x),\rev(x)) \\
 & = & \suffix(x,x)
\end{eqnarray*}$$
as claimed.
2. If $\suffix(x,y)$, we have $y = \cat(u,x)$ for some $u$. Similarly, if $\suffix(y,x)$ then $x = \cat(v,y)$ for some $v$. Now
$$\begin{eqnarray*}
 &   & \cat(\nil,x) \\
 & = & x \\
 & = & \cat(v,y) \\
 & = & \cat(v,\cat(u,x)) \\
 & = & \cat(\cat(v,u),x).
\end{eqnarray*}$$
Since $\cat$ is cancellative, we have $\nil = \cat(v,u)$, so that $u = \nil$, and thus $x = y$ as claimed.
3. If $\suffix(x,y)$ and $\suffix(y,z)$, then $\prefix(\rev(x),\rev(y))$ and $\prefix(\rev(y),\rev(z))$. So $\prefix(\rev(x),\rev(z))$, and thus $\suffix(x,z)$.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_reflexive :: (List t, Equal a)
>   => t a -> Test (t a -> Bool)
> _test_suffix_reflexive _ =
>   testName "suffix(x,x) == true" $
>   \x -> eq (suffix x x) true
> 
> 
> _test_suffix_symmetric :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_suffix_symmetric _ =
>   testName "suffix(x,y) & suffix(y,x) ==> eq(x,y)" $
>   \x y -> if and (suffix x y) (suffix y x)
>     then eq x y
>     else true
> 
> 
> _test_suffix_transitive :: (List t, Equal a)
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_suffix_transitive _ =
>   testName "suffix(x,y) & suffix(y,z) ==> suffix(x,z)" $
>   \x y z -> if and (suffix x y) (suffix y z)
>     then suffix x z
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\map$ preserves suffixes:

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$, and let $x,y \in \lists{A}$. If $\suffix(x,y) = \btrue$, then $$\suffix(\map(f)(x),\map(f)(y)) = \btrue.$$

::: proof ::::::::::
Suppose $\suffix(x,y)$; then $\prefix(\rev(x),\rev(y))$. Then we have
$$\begin{eqnarray*}
 &   & \suffix(\map(f)(x),\map(f)(y)) \\
 & = & \prefix(\rev(\map(f)(x)),\rev(\map(f)(y))) \\
 & = & \prefix(\map(f)(\rev(x)),\map(f)(\rev(y))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_map :: (List t, Equal a)
>   => t a -> Test ((a -> a) -> t a -> t a -> Bool)
> _test_suffix_map _ =
>   testName "if suffix(x,y) then suffix(map(f)(x),map(f)(y))" $
>   \f x y -> if suffix x y
>     then suffix (map f x) (map f y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

$\suffix$ interacts with $\length$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. If $\suffix(x,y)$, then $\nleq(\length(x),\length(y))$.

::: proof ::::::::::
Suppose $\suffix(x,y)$. Then $\prefix(\rev(x),\rev(y))$, so we have
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\length(\rev(x),\length(\rev(y)))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_suffix_length :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (t a -> t a -> Bool)
> _test_suffix_length _ k =
>   testName "if suffix(x,y) then leq(length(x),length(y))" $
>   \x y -> if suffix x y
>     then leq ((length x) `withTypeOf` k) (length y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

As a special case, the prefixes and suffixes of a one-element list coincide.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\prefix(x,\cons(a,\nil)) = \suffix(x,\cons(a,\nil)).$$

::: proof ::::::::::
We consider three possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,\cons(a,\nil)) \\
 & = & \prefix(\nil,\cons(a,\nil)) \\
 & = & \btrue \\
 & = & \suffix(\nil,\cons(a,\nil)) \\
 & = & \suffix(x,\cons(a,\nil))
\end{eqnarray*}$$
as needed. If $x = \cons(b,\nil)$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,\cons(a,\nil)) \\
 & = & \prefix(\cons(b,\nil),\cons(a,\nil)) \\
 & = & \bif{\beq(a,b)}{\prefix(\nil,\nil)}{\bfalse} \\
 & = & \bif{\beq(a,b)}{\btrue}{\bfalse} \\
 & = & \bif{\beq(a,b)}{\suffix(\nil,\nil)}{\bfalse} \\
 & = & \suffix(\snoc(b,\nil),\snoc(a,\nil)) \\
 & = & \suffix(\cons(b,\nil),\cons(a,\nil)) \\
 & = & \suffix(x,\cons(a,\nil))
\end{eqnarray*}$$
as needed. Finally, suppose $x = \cons(b,\cons(c,u))$ for some $u$. In this case we have
$$\begin{eqnarray*}
 &   & \nleq(\next(\length(\cons(a,\nil))),\length(x)) \\
 & = & \nleq(\next(\next(\zero)),\length(\cons(b,\cons(c,u)))) \\
 & = & \nleq(\next(\next(\zero)),\next(\next(\length(u)))) \\
 & = & \nleq(\zero,\length(u)) \\
 & = & \btrue,
\end{eqnarray*}$$
so that $\prefix(x,\cons(a,\nil)) = \bfalse$. Similarly, $$\nleq(\next(\length(\cons(a,\nil))),\length(x)) = \btrue$$ so that $\suffix(x,\cons(a,\nil)) = \bfalse$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_prefix_suffix_singleton :: (List t, Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_prefix_suffix_singleton _ =
>   testName "prefix(x,cons(a,nil)) == suffix(x,cons(a,nil))" $
>   \a x -> eq (prefix x (cons a nil)) (suffix x (cons a nil))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_prefix_suffix ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Equal n, Natural n, Show n, Arbitrary n
>   , Show (t a), Equal (t a), Arbitrary (t a)
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_prefix_suffix t n maxSize numCases = do
>   testLabel2 "prefix & suffix" t n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_prefix_nil_list t)
>   runTest args (_test_prefix_cons_nil t)
>   runTest args (_test_prefix_cons_cons t)
>   runTest args (_test_prefix_cat t)
>   runTest args (_test_prefix_snoc t)
>   runTest args (_test_prefix_reflexive t)
>   runTest args (_test_prefix_symmetric t)
>   runTest args (_test_prefix_transitive t)
>   runTest args (_test_prefix_map t)
>   runTest args (_test_prefix_zip t)
>   runTest args (_test_prefix_length t n)
> 
>   runTest args (_test_suffix_prefix t)
>   runTest args (_test_suffix_nil_list t)
>   runTest args (_test_suffix_snoc_nil t)
>   runTest args (_test_suffix_snoc_snoc t)
>   runTest args (_test_suffix_cat t)
>   runTest args (_test_suffix_cons t)
>   runTest args (_test_suffix_reflexive t)
>   runTest args (_test_suffix_symmetric t)
>   runTest args (_test_suffix_transitive t)
>   runTest args (_test_suffix_map t)
>   runTest args (_test_suffix_length t n)
> 
>   runTest args (_test_prefix_suffix_singleton t)

Main:

> main_prefix_suffix :: IO ()
> main_prefix_suffix = do
>   _test_prefix_suffix (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_prefix_suffix (nil :: ConsList Unary) (zero :: Unary) 20 100
