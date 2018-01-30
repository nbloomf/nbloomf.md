---
title: Filter
author: nbloomf
date: 2017-05-13
tags: arithmetic-made-difficult, literate-haskell
slug: filter
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Filter
>   ( filter, _test_filter, main_filter
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits

Today we'll nail down $\filter$, which takes a list and a predicate on the items and "filters out" the items which satisfy the predicate. $\filter$ should have a signature like $$\bool^A \times \lists{A} \rightarrow \lists{A}.$$ As usual, we want to define $\filter$ as a fold; say $$\filter(p)(x) = \foldr{\varepsilon}{\varphi}(x).$$ Where on the right hand side of that equation should the $p$ parameter go? Lets think out loud for a moment. On the one hand, we want
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \filter(p)(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil) \\
 & = & \varepsilon.
\end{eqnarray*}$$
On the other hand, we want
$$\begin{eqnarray*}
 &   & \filter(p)(\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(a,\filter(p)(x)).
\end{eqnarray*}$$
Intuitively, if $p(a)$ is $\btrue$ we want $$\filter(p)(\cons(a,x)) = \cons(a,\filter(p)(x)),$$ while if $p(a)$ is $\bfalse$ we want $$\filter(p)(\cons(a,x)) = \filter(p)(x).$$ With this in mind we define $\filter$ like so.

:::::: definition ::
Let $A$ be a set. Define $\varphi : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(a,w) = \left\{ \begin{array}{ll} \cons(a,w) & \mathrm{if}\ p(a) = \btrue \\ w & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$ Now define $$\filter : \bool^A \rightarrow {\lists{A}}^{\lists{A}}$$ by $$\filter(p)(x) = \foldr{\nil}{\varphi}(x).$$

In Haskell:

> filter :: (List t) => (a -> Bool) -> t a -> t a
> filter p x = foldr nil phi x
>   where
>     phi a w = if eq (p a) true
>       then cons a w
>       else w

::::::::::::::::::::

Since $\filter(p)$ is defined as a $\foldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. $\filter(p)$ is the unique map $f : \lists{A} \rightarrow \lists{A}$ satisfying the following for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{ll}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \bif{p(a)}{\cons(a,f(x))}{f(x)}
\end{array}\right.$$

::: test :::::::::::

> _test_filter_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> Bool)
> _test_filter_nil t =
>   testName "filter(p)(nil) == nil" $
>   \p -> eq (filter p (nil `withTypeOf` t)) nil
> 
> 
> _test_filter_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_filter_cons _ =
>   testName "filter(p)(cons(a,x)) == if(p(a),cons(a,filter(p)(x)),filter(p)(x))" $
>   \p a x -> eq
>     (filter p (cons a x))
>     (if p a then cons a (filter p x) else filter p x)

::::::::::::::::::::
::::::::::::::::::::

As we might expect, the items in $\filter(p)(x)$ all satisfy $p$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$ we have $$\all(p,\filter(p)(x)) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p)(\nil)) \\
 & = & \all(p,\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p)(\cons(a,x))) \\
 & = & \all(p,\cons(a,\filter(p)(x))) \\
 & = & \band(p(a),\all(p,\filter(p)(x))) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as claimed, while if $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p)(\cons(a,x))) \\
 & = & \all(p,\filter(p)(x)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_all :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_filter_all _ =
>   testName "all(p,filter(p)(x)) == true" $
>   \p x -> eq (all p (filter p x)) true

::::::::::::::::::::
::::::::::::::::::::

$\filter$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $a \in A$ and $x \in \lists{A}$, we have $$\filter(p)(\snoc(a,x)) = \bif{p(a)}{\snoc(a,\filter(p)(x))}{\filter(p)(x)}.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, if $p(a) = \btrue$ we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\nil)) \\
 & = & \filter(p)(\cons(a,\nil)) \\
 & = & \cons(a,\filter(p)(\nil)) \\
 & = & \cons(a,\nil) \\
 & = & \snoc(a,\nil)
\end{eqnarray*}$$
as claimed, while if $p(a) = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\nil)) \\
 & = & \filter(p)(\cons(a,\nil)) \\
 & = & \filter(p)(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. If $p(a) = p(b) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\cons(b,x))) \\
 & = & \filter(p)(\cons(b,\snoc(a,x))) \\
 & = & \cons(b,\filter(p)(\snoc(a,x))) \\
 & = & \cons(b,\snoc(a,\filter(p)(x))) \\
 & = & \snoc(a,\cons(b,\filter(p)(x))) \\
 & = & \snoc(a,\filter(p)(\cons(b,x)))
\end{eqnarray*}$$
as needed. If $p(a) = \btrue$ and $p(b) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\cons(b,x))) \\
 & = & \filter(p)(\cons(b,\snoc(a,x))) \\
 & = & \filter(p)(\snoc(a,x)) \\
 & = & \snoc(a,\filter(p)(x)) \\
 & = & \snoc(a,\filter(p)(\cons(b,x)))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$ and $p(b) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\cons(b,x))) \\
 & = & \filter(p)(\cons(b,\snoc(a,x))) \\
 & = & \cons(b,\filter(p)(\snoc(a,x))) \\
 & = & \cons(b,\filter(p)(x)) \\
 & = & \filter(p)(\cons(b,x))
\end{eqnarray*}$$
as needed. Finally, if $p(a) = p(b) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\snoc(a,\cons(b,x))) \\
 & = & \filter(p)(\cons(b,\snoc(a,x))) \\
 & = & \filter(p)(\snoc(a,x)) \\
 & = & \filter(p)(x) \\
 & = & \filter(p)(\cons(b,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_filter_snoc _ =
>   testName "filter(p)(snoc(a,x)) == if(p(a),snoc(a,filter(p)(x)),filter(p)(x))" $
>   \p a x -> eq
>     (filter p (snoc a x))
>     (if p a then snoc a (filter p x) else filter p x)

::::::::::::::::::::
::::::::::::::::::::

$\filter$ interacts with $\rev$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$, we have $$\filter(p)(\rev(x)) = \rev(\filter(p)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\rev(\nil)) \\
 & = & \filter(p)(\nil) \\
 & = & \nil \\
 & = & \rev(\nil) \\
 & = & \rev(\filter(p)(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \rev(\filter(p)(\cons(a,x))) \\
 & = & \rev(\cons(a,\filter(p)(x))) \\
 & = & \snoc(a,\rev(\filter(p)(x))) \\
 & = & \snoc(a,\filter(p)(\rev(x))) \\
 & = & \filter(p)(\snoc(a,\rev(x))) \\
 & = & \filter(p)(\rev(\cons(a,x)))
\end{eqnarray*}$$
as claimed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \rev(\filter(p)(\cons(a,x))) \\
 & = & \rev(\filter(p)(x)) \\
 & = & \filter(p)(\rev(x)) \\
 & = & \filter(p)(\snoc(a,\rev(x))) \\
 & = & \filter(p)(\rev(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_filter_rev _ =
>   testName "filter(p)(rev(x)) == rev(filter(p)(x))" $
>   \p x -> eq (filter p (rev x)) (rev (filter p x))

::::::::::::::::::::
::::::::::::::::::::

$\filter(p)$ distributes over $\cat$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x,y \in \lists{A}$ we have $$\filter(p)(\cat(x,y)) = \cat(\filter(p)(x),\filter(p)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\cat(x,y)) \\
 & = & \filter(p)(\cat(\nil,y)) \\
 & = & \filter(p)(y) \\
 & = & \cat(\nil,\filter(p)(y)) \\
 & = & \cat(\filter(p)(\nil),\filter(p)(y)) \\
 & = & \cat(\filter(p)(x),\filter(p)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\cat(\cons(a,x),y)) \\
 & = & \filter(p)(\cons(a,\cat(x,y))) \\
 & = & \cons(a,\filter(p)(\cat(x,y))) \\
 & = & \cons(a,\cat(\filter(p)(x),\filter(p)(y))) \\
 & = & \cat(\cons(a,\filter(p)(x)),\filter(p)(y)) \\
 & = & \cat(\filter(p)(\cons(a,x)),\filter(p)(y))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\cat(\cons(a,x),y)) \\
 & = & \filter(p)(\cons(a,\cat(x,y))) \\
 & = & \filter(p)(\cat(x,y)) \\
 & = & \cat(\filter(p)(x),\filter(p)(y)) \\
 & = & \cat(\filter(p)(\cons(a,x)),\filter(p)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_filter_cat _ =
>   testName "filter(p)(cat(x,y)) == cat(filter(p)(x),filter(p)(y))" $
>   \p x y -> eq (filter p (cat x y)) (cat (filter p x) (filter p y))

::::::::::::::::::::
::::::::::::::::::::

$\filter(p)$ is idempotent.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$ we have $$\filter(p)(\filter(p)(x)) = \filter(p)(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\filter(p)(x)) \\
 & = & \filter(p)(\filter(p)(\nil)) \\
 & = & \filter(p)(\nil) \\
 & = & \nil \\
 & = & x
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \filter(p)(\filter(p)(\cons(a,x))) \\
 & = & \filter(p)(\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{p(a)}{\filter(p)(\cons(a,\filter(p)(x)))}{\filter(p)(\filter(p)(x))} \\
 & = & \bif{p(a)}{\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}}{\filter(p)(x)} \\
 &     \href{@booleans@#thm-if-prune-true}
   = & \bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)} \\
 & = & \filter(p)(\cons(a,x))
\end{eqnarray*}$$
as needed
::::::::::::::::::::

::: test :::::::::::

> _test_filter_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_filter_idempotent _ =
>   testName "filter(p)(filter(p)(x)) == filter(p)(x)" $
>   \p x -> eq (filter p (filter p x)) (filter p x)

::::::::::::::::::::
::::::::::::::::::::

A list $x$ is invariant under $\filter(p)$ if and only if $\all(p)(x)$.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate with $x \in \lists{A}$. We have $$\beq(x,\filter(p)(x)) = \all(p,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(x,\filter(p)(x)) \\
 & = & \beq(\nil,\filter(p)(\nil)) \\
 & = & \beq(\nil,\nil) \\
 &     \href{@booleans@#thm-eq-reflexive}
   = & \btrue \\
 & = & \all(p,\nil) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. We consider two possibilities. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,x),\filter(p)(\cons(a,x))) \\
 & = & \beq(\cons(a,x),\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 & = & \beq(\cons(a,x),\bif{\btrue}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 &     \href{@booleans@#cor-if-true}
   = & \beq(\cons(a,x),\cons(a,\filter(p)(x))) \\
 & = & \band(\beq(a,a),\beq(x,\filter(p)(x))) \\
 &     \href{@booleans@#thm-eq-reflexive}
   = & \band(\btrue,\beq(x,\filter(p)(x))) \\
 &     \href{@and@#thm-and-true-left}
   = & \beq(x,\filter(p)(x)) \\
 & = & \all(p,x) \\
 &     \href{@and@#thm-and-true-left}
   = & \band(\btrue,\all(p,x)) \\
 & = & \band(p(a),\all(p,x)) \\
 & = & \all(p,\cons(a,x))
\end{eqnarray*}$$
as needed. Suppose instead that $p(a) = \bfalse$. Now $\sublist(\filter(p)(x),x) = \btrue$, and using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,x),\filter(p)(\cons(a,x))) \\
 & = & \beq(\cons(a,x),\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 & = & \beq(\cons(a,x),\bif{\bfalse}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 &     \href{@booleans@#cor-if-false}
   = & \beq(\cons(a,x),\filter(p)(x)) \\
 & = & \bfalse \\
 &     \href{@and@#thm-and-false-left}
   = & \band(\bfalse,\all(p,x)) \\
 & = & \band(p(a),\all(p,x)) \\
 & = & \all(p,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_eq_all :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_filter_eq_all _ =
>   testName "eq(x,filter(p)(x)) == all(p,x)" $
>   \p x -> eq (eq x (filter p x)) (all p x)

::::::::::::::::::::
::::::::::::::::::::

$\filter(p)$ and $\filter(q)$ commute.

:::::: theorem :::::
Let $A$ be a set and $p,q : A \rightarrow \bool$ predicates. For all $x \in \lists{A}$ we have $$\filter(p)(\filter(q)(x)) = \filter(q)(\filter(p)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p)(\filter(q)(\nil)) \\
 & = & \filter(p)(\nil) \\
 & = & \nil \\
 & = & \filter(q)(\nil) \\
 & = & \filter(q)(\filter(p)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \filter(p)(\filter(q)(\cons(a,x))) \\
 & = & \filter(p)(\bif{q(a)}{\cons(a,\filter(q)(x))}{\filter(q)(x)}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{q(a)}{\filter(p)(\cons(a,\filter(q)(x)))}{\filter(p)(\filter(q)(x))} \\
 & = & \bif{q(a)}{\bif{p(a)}{\cons(a),\filter(p)(\filter(q)(x))}{\filter(p)(\filter(q)(x))}}{\filter(p)(\filter(q)(x))} \\
 & = & \bif{p(a)}{\bif{q(a)}{\cons(a),\filter(p)(\filter(q)(x))}{\filter(p)(\filter(q)(x))}}{\filter(p)(\filter(q)(x))} \\
 & = & \bif{p(a)}{\filter(q)(\cons(a,\filter(p)(x)))}{\filter(q)(\filter(p)(x))} \\
 &     \href{@booleans@#thm-iffunc}
   = & \filter(q)(\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 & = & \filter(q)(\filter(p)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_filter_commute :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> (a -> Bool) -> t a -> Bool)
> _test_filter_commute _ =
>   testName "filter(p)(filter(q)(x)) == filter(q)(filter(p)(x))" $
>   \p q x -> eq (filter p (filter q x)) (filter q (filter p x))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_filter ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a))
>   ) => t a -> Int -> Int -> IO ()
> _test_filter t maxSize numCases = do
>   testLabel1 "filter" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_filter_nil t)
>   runTest args (_test_filter_cons t)
>   runTest args (_test_filter_all t)
>   runTest args (_test_filter_snoc t)
>   runTest args (_test_filter_rev t)
>   runTest args (_test_filter_cat t)
>   runTest args (_test_filter_idempotent t)
>   runTest args (_test_filter_eq_all t)
>   runTest args (_test_filter_commute t)

Main:

> main_filter :: IO ()
> main_filter = do
>   _test_filter (nil :: ConsList Bool)  20 100
>   _test_filter (nil :: ConsList Unary) 20 100
