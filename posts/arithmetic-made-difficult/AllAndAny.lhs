---
title: All and Any
author: nbloomf
date: 2017-05-10
tags: arithmetic-made-difficult, literate-haskell
slug: all-any
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module AllAndAny
>   ( all, any, _test_all_any, main_all_any
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Predicates
> import NaturalNumbers
> import Lists
> import Snoc
> import Reverse
> import Map
> import Cat
> import Zip
> import PrefixAndSuffix

Today we'll define two boolean functions for lists called $\all$ and $\any$. Each one takes as an argument a predicate $A \rightarrow \bool$, and then tests whether all or any of the items in a list of type $\lists{A}$ satisfy the predicate.

:::::: definition ::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. Define $\varphi : A \times \bool \rightarrow \bool$ by $$\varphi(a,q) = \band(p(a),q).$$ Now define $\all : \bool^A \rightarrow \bool^{\lists{A}}$ by $$\all(p)(x) = \foldr{\btrue}{\varphi}(x).$$

In Haskell:

> all :: (Boolean b, List t) => (a -> b) -> t a -> b
> all p = foldr true phi
>   where
>     phi a q = and (p a) q

::::::::::::::::::::

Since $\all(p)$ is defined as a $\foldr{\ast}{\ast}$, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. Then $\all(p)$ is the unique solution $f : \lists{A} \rightarrow \bool$ to the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \btrue \\
 f(\cons(a,x)) = \band(p(a),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_all_nil :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> Bool)
> _test_all_nil t =
>   testName "all(p)(nil) == true" $
>   \p -> all p (nil `withTypeOf` t)
> 
> 
> _test_all_cons :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_all_cons _ =
>   testName "all(p)(cons(a,x)) == and(p(a),all(p)(x))" $
>   \p a x -> eq (all p (cons a x)) (and (p a) (all p x))

::::::::::::::::::::
::::::::::::::::::::

$\all$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $p : A \rightarrow \bool$, $a \in A$, and $x \in \lists{A}$, we have $$\all(p,\snoc(a,x)) = \band(p(a),\all(p,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\snoc(a,x)) \\
 & = & \all(p,\snoc(a,\nil)) \\
 & = & \all(p,\cons(a,\nil)) \\
 & = & \band(p(a),\all(p,\nil)) \\
 & = & \band(p(a),\all(p,x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $p$ and $a$ for some $x$ and let $b \in A$. Using the inductive step, we have
$$\begin{eqnarray*}
 &   & \all(p,\snoc(a,\cons(b,x))) \\
 & = & \all(p,\cons(b,\snoc(a,x))) \\
 & = & \band(p(b),\all(p,\snoc(a,x))) \\
 & = & \band(p(b),\band(p(a),\all(p,x))) \\
 & = & \band(p(a),\band(p(b),\all(p,x))) \\
 & = & \band(p(a),\all(p,\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_snoc :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_all_snoc _ =
>   testName "all(p)(snoc(a,x)) == and(p(a),all(p)(x))" $
>   \p a x -> eq (all p (snoc a x)) (and (p a) (all p x))

::::::::::::::::::::
::::::::::::::::::::

$\all$ can also be characterized as a folded map.

:::::: theorem :::::
$$\all(p,x) = \foldr{\btrue}{\band}(\map(p)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,x) \\
 & = & \all(p,\nil) \\
 & = & \btrue \\
 & = & \foldr{\btrue}{\band}(\nil) \\
 & = & \foldr{\btrue}{\band}(\map(p)(\nil)) \\
 & = & \foldr{\btrue}{\band}(\map(p)(x))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p,\cons(a,x)) \\
 & = & \band(p(a),\all(p,x)) \\
 & = & \band(p(a),\foldr{\btrue}{\band}(\map(p)(x))) \\
 & = & \foldr{\btrue}{\band}(\cons(p(a),\map(p)(x))) \\
 & = & \foldr{\btrue}{\band}(\map(p)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_fold_and :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_all_fold_and _ =
>   testName "all(p,x) == foldr(true,and)(map(p)(x))" $
>   \p x -> eq (all p x) (foldr true and (map p x))

::::::::::::::::::::
::::::::::::::::::::

Two special cases.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. The following hold for all $x \in \lists{A}$.

1. $\all(\ptrue)(x) = \btrue$.
2. $\all(\pfalse)(x) = \bfalse$ if and only if $x \neq \nil$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\ptrue,x) \\
 & = & \all(\ptrue,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(\ptrue)(\cons(a,x)) \\
 & = & \band(\ptrue(a),\all(\ptrue)(x)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\pfalse)(\nil) \\
 & = & \btrue,
\end{eqnarray*}$$
while if $x = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \all(\pfalse)(\cons(a,u)) \\
 & = & \band(\pfalse(a),\all(\pfalse)(u)) \\
 & = & \band(\bfalse,\all(\pfalse)(u)) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_const_true :: (List t, Equal a, Boolean b, Equal b)
>   => t a -> b -> Test (t a -> Bool)
> _test_all_const_true _ p =
>   testName "all(ptrue)(x) == true" $
>   \x -> eq (all ptrue x) (true `withTypeOf` p)
> 
> 
> _test_all_const_false :: (List t, Equal a, Equal (t a), Boolean b, Equal b)
>   => t a -> b -> Test (t a -> Bool)
> _test_all_const_false _ p =
>   testName "all(pfalse)(x) == false iff x /= nil" $
>   \x -> eq
>     ((eq (all pfalse x) (false `withTypeOf` p)) `withTypeOf` p)
>     (not (eq x nil))

::::::::::::::::::::
::::::::::::::::::::

$\all$ interacts with $\cat$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x,y \in \lists{A}$ we have $$\all(p,\cat(x,y)) = \band(\all(p)(x),\all(p)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p)(\cat(x,y)) \\
 & = & \all(p)(\cat(\nil,y)) \\
 & = & \all(p)(y) \\
 & = & \band(\btrue,\all(p)(y)) \\
 & = & \band(\all(p)(\nil),\all(p)(y)) \\
 & = & \band(\all(p)(x),\all(p)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p)(\cat(\cons(a,x),y)) \\
 & = & \all(p)(\cons(a,\cat(x,y))) \\
 & = & \band(p(a),\all(p)(\cat(x,y))) \\
 & = & \band(p(a),\band(\all(p)(x),\all(p)(y))) \\
 & = & \band(\band(p(a),\all(p)(x)),\all(p)(y)) \\
 & = & \band(\all(p)(\cons(a,x)),\all(p)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_cat :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_all_cat _ =
>   testName "all(p,cat(x,y)) == all(p,x) && all(p,y)" $
>   \p x y -> eq (all p (cat x y)) (and (all p x) (all p y))

::::::::::::::::::::
::::::::::::::::::::

$\all$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x \in \lists{A}$ we have $$\all(p,\rev(x)) = \all(p,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\rev(x)) \\
 & = & \all(p,\rev(\nil)) \\
 & = & \all(p,\nil) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \all(p,\rev(\cons(a,x))) \\
 & = & \all(p,\rev(\cat(\cons(a,\nil),x))) \\
 & = & \all(p,\cat(\rev(x),\rev(\cons(a,\nil)))) \\
 & = & \band(\all(p,\rev(x)),\all(p,\rev(\cons(a,\nil)))) \\
 & = & \band(\all(p,x),\all(p,\cons(a,\nil))) \\
 & = & \band(\all(p,\cons(a,\nil)),\all(p,x)) \\
 & = & \all(p,\cat(\cons(a,\nil),x)) \\
 & = & \all(p,\cons(a,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_rev :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_all_rev _ =
>   testName "all(p,rev(x)) == all(p,x)" $
>   \p x y -> eq (all p (rev x)) (all p x)

::::::::::::::::::::
::::::::::::::::::::

$\all$ interacts with $\pimpl$.

:::::: theorem :::::
Let $A$ be a set and $p,q : A \rightarrow \bool$. If $\pimpl(p,q)$, then $$\bimpl(\all(p,x),\all(q,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\all(p,\nil),\all(q,\nil)) \\
 & = & \bimpl(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. Now $\bimpl(p(a),q(a))$, and by the induction hypothesis $\bimpl(\all(p,x),\all(q,x))$. Then we have
$$\begin{eqnarray*}
 &   & \bimpl(\all(p,\cons(a,x)),\all(q,\cons(a,x))) \\
 & = & \bimpl(\band(p(a),\all(p,x)),\band(q(a),\all(q),x))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

$\all$ interacts with $\map$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ and $p : B \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\all(p)(\map(f)(x)) = \all(p \circ f)(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p)(\map(f)(x)) \\
 & = & \all(p)(\map(f)(\nil)) \\
 & = & \all(p)(\nil) \\
 & = & \btrue \\
 & = & \all(p \circ f)(\nil) \\
 & = & \all(p \circ f)(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p)(\map(f)(\cons(a,x))) \\
 & = & \all(p)(\cons(f(a),\map(f)(x))) \\
 & = & \band(p(f(a)),\all(p)(\map(f)(x))) \\
 & = & \band((p \circ f)(a),\all(p \circ f)(x)) \\
 & = & \all(p \circ f)(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_all_map :: (List t, Equal a)
>   => t a -> Test ((a -> a) -> (a -> Bool) -> t a -> Bool)
> _test_all_map _ =
>   testName "all(p)(map(f)(x)) == all(p . f)(x)" $
>   \f p x -> eq (all p (map f x)) (all (p . f) x)

::::::::::::::::::::
::::::::::::::::::::

$\any$ is defined similarly.

:::::: definition ::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. Define $\varphi : A \times \bool \rightarrow \bool$ by $$\varphi(a,q) = \bor(p(a),q).$$ Now define $\any : \bool^A \rightarrow \bool^{\lists{A}}$ by $$\all(p)(x) = \foldr{\bfalse}{\varphi}(x).$$

In Haskell:

> any :: (Boolean b, List t) => (a -> b) -> t a -> b
> any p = foldr false phi
>   where
>     phi a q = or (p a) q

::::::::::::::::::::

Since $\any$ is defined as a fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set and $p$ a predicate on $A$. $\any(p)$ is the unique map $f : \lists{A} \rightarrow \bool$ satisfying the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \bfalse \\
 f(\cons(a,x)) = \bor(p(a),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_any_nil :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> Bool)
> _test_any_nil t =
>   testName "any(p)(nil) == false" $
>   \p -> eq (any p (nil `withTypeOf` t)) false
> 
> 
> _test_any_cons :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_any_cons _ =
>   testName "any(p)(cons(a,x)) == or(p(a),any(p)(x))" $
>   \p a x -> eq (any p (cons a x)) (or (p a) (any p x))

::::::::::::::::::::
::::::::::::::::::::

$\any$ can also be characterized as a folded map.

:::::: theorem :::::
Let $A$ be a set with $p$ a predicate on $A$. Then $$\any(p,x) = \foldr{\bfalse}{\bor}(\map(p)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \any(p,x) \\
 & = & \any(p,\nil) \\
 & = & \bfalse \\
 & = & \foldr{\bfalse}{\bor}(\nil) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(\nil)) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \any(p,\cons(a,x)) \\
 & = & \bor(p(a),\any(x)) \\
 & = & \bor(p(a),\foldr{\bfalse}{\bor}(\map(p)(x))) \\
 & = & \foldr{\bfalse}{\bor}(\cons(p(a),\map(p)(x))) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_fold_or :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_any_fold_or _ =
>   testName "any(p,x) == foldr(false,or)(map(p)(x))" $
>   \p x -> eq (any p x) (foldr false or (map p x))

::::::::::::::::::::
::::::::::::::::::::

A version of DeMorgan's law holds for $\any$ and $\all$.

:::::: theorem :::::
Let $A$ be a set with $p : A \rightarrow \bool$. Then the following hold for all $x \in \lists{A}$.

1. $\any(p,x) = \bnot(\all(\bnot \circ p,x))$.
2. $\all(p,x) = \bnot(\any(\bnot \circ p,x))$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \bnot(\all(\not \circ p,x)) \\
 & = & \bnot(\all(\not \circ p,\nil)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse \\
 & = & \foldr{\bfalse}{\varphi(p)}(\nil) \\
 & = & \foldr{\bfalse}{\varphi(p)}(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \bnot(\all(\bnot \circ p,\cons(a,x))) \\
 & = & \bnot(\band(\bnot(p(a)),\all(\bnot \circ p,x))) \\
 & = & \bor(\bnot(\bnot(p(a))),\bnot(\all(\bnot \circ p,x))) \\
 & = & \bor(p(a),\any(p,x)) \\
 & = & \any(p,\cons(a,x))
\end{eqnarray*}$$
as needed.
2. Note that
$$\begin{eqnarray*}
 &   & \bnot(\any(\bnot \circ p,x)) \\
 & = & \bnot(\bnot(\all(\bnot \circ \bnot \circ p,x))) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_not_all :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_any_not_all _ =
>   testName "any(p,x) == not(all(not . p, x))" $
>   \p x -> eq (any p x) (not (all (not . p) x))
> 
> 
> _test_all_not_any :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_all_not_any _ =
>   testName "all(p,x) == not(any(not . p, x))" $
>   \p x -> eq (all p x) (not (any (not . p) x))

::::::::::::::::::::
::::::::::::::::::::

Two special cases.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. The following hold for all $x \in \lists{A}$.

1. $\any(\pfalse)(x) = \bfalse$.
2. $\any(\ptrue)(x) = \btrue$ if and only if $x \neq \nil$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \any(\pfalse)(x) \\
 & = & \bnot(\all(\bnot \circ \pfalse)(x)) \\
 & = & \bnot(\all(\ptrue)(x)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
2. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \any(\pfalse)(x) \\
 & = & \btrue,
\end{eqnarray*}$$
while if $x = \cons(a,u)$ we have
$$\begin{eqnarray*}
 &   & \any(\ptrue)(\cons(a,u)) \\
 & = & \bnot(\all(\bnot \circ \ptrue)(\cons(a,u))) \\
 & = & \bnot(\all(\pfalse)(\cons(a,u))) \\
 & = & \bnot(\bfalse) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_const_false :: (List t, Equal a, Boolean b, Equal b)
>   => t a -> b -> Test (t a -> Bool)
> _test_any_const_false _ p =
>   testName "any(pfalse,x) == false" $
>   \x -> eq (any pfalse x) (false `withTypeOf` p)
> 
> 
> _test_any_const_true :: (List t, Equal a, Equal (t a), Boolean b, Equal b)
>   => t a -> b -> Test (t a -> Bool)
> _test_any_const_true _ p =
>   testName "any(ptrue,x) == true iff x /= nil" $
>   \x -> eq
>     ((eq (any ptrue x) (true `withTypeOf` p)) `withTypeOf` p)
>     (not (eq x nil))

::::::::::::::::::::
::::::::::::::::::::

$\any$ interacts with $\cat$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x,y \in \lists{A}$ we have $$\any(p,\cat(x,y)) = \bor(\any(p)(x),\any(p)(y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \any(p,\cat(x,y)) \\
 & = & \bnot(\all(\bnot \circ p,\cat(x,y))) \\
 & = & \bnot(\band(\all(\bnot \circ p,x),\all(\bnot \circ p,y))) \\
 & = & \bor(\bnot(\all(\bnot \circ p,x)),\bnot(\all(\bnot \circ p,y))) \\
 & = & \bor(\any(p,x),\any(p,y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_cat :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_any_cat _ =
>   testName "any(p,cat(x,y)) == any(p,x) || any(p,y)" $
>   \p x y -> eq (any p (cat x y)) (or (any p x) (any p y))

::::::::::::::::::::
::::::::::::::::::::

$\any$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x,y \in \lists{A}$ we have $$\any(p,\rev(x)) = \any(p,x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \any(p,\rev(x)) \\
 & = & \bnot(\all(\bnot \circ p,\rev(x))) \\
 & = & \bnot(\all(\bnot \circ p,x)) \\
 & = & \any(p,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_rev :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_any_rev _ =
>   testName "any(p,rev(x)) == any(p,x)" $
>   \p x y -> eq (any p (rev x)) (any p x)

::::::::::::::::::::
::::::::::::::::::::

$\any$ interacts with $\map$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$ and $p : B \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\any(p)(\map(f)(x)) = \any(p \circ f)(x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \any(p,\map(f)(x)) \\
 & = & \bnot(\all(\bnot \circ p,\map(f)(x))) \\
 & = & \bnot(\all((\bnot \circ p) \circ f,x)) \\
 & = & \bnot(\all(\bnot \circ (p \circ f),x)) \\
 & = & \any(p \circ f,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_any_map :: (List t, Equal a)
>   => t a -> Test ((a -> a) -> (a -> Bool) -> t a -> Bool)
> _test_any_map _ =
>   testName "any(p)(map(f)(x)) == any(p . f)(x)" $
>   \f p x -> eq (any p (map f x)) (any (p . f) x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_all_any ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a)
>   , TypeName b, Boolean b, Equal b
>   ) => t a -> b -> Int -> Int -> IO ()
> _test_all_any t p maxSize numCases = do
>   testLabel1 "all & any" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_all_nil t)
>   runTest args (_test_all_cons t)
>   runTest args (_test_all_snoc t)
>   runTest args (_test_all_fold_and t)
>   runTest args (_test_all_const_true t p)
>   runTest args (_test_all_const_false t p)
>   runTest args (_test_all_cat t)
>   runTest args (_test_all_rev t)
>   runTest args (_test_all_map t)
> 
>   runTest args (_test_any_nil t)
>   runTest args (_test_any_cons t)
>   runTest args (_test_any_fold_or t)
>   runTest args (_test_any_not_all t)
>   runTest args (_test_all_not_any t)
>   runTest args (_test_all_const_false t p)
>   runTest args (_test_all_const_true t p)
>   runTest args (_test_any_cat t)
>   runTest args (_test_any_rev t)
>   runTest args (_test_any_map t)

Main:

> main_all_any :: IO ()
> main_all_any = do
>   _test_all_any (nil :: ConsList Bool)  (true :: Bool) 20 100
>   _test_all_any (nil :: ConsList Unary) (true :: Bool) 20 100
