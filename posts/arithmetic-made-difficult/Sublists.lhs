---
title: Sublists
author: nbloomf
date: 2018-01-20
tags: arithmetic-made-difficult, literate-haskell
slug: sublists
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Sublists (
>   sublists, _test_sublists, main_sublists
> ) where
> 
> import Testing
> import Booleans
> import Unary
> import NaturalNumbers
> import Exponentiation
> import Lists
> import Snoc
> import Cat
> import Length
> import Map
> import AllAndAny
> import Filter
> import Elt
> import Sublist
> import Select
> import Unique

We've already defined a predicate that detects when one list is a sublist of another. Today we'll define a function that constructs a list of all sublists of a given list.

:::::: definition ::
Let $A$ be a set. Define $\varphi : A \times \lists{\lists{A}} \rightarrow \lists{\lists{A}}$ by $$\varphi(a,z) = \cat(\map(\cons(a,-)(z)),z).$$ Now define $\sublists : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\sublists = \foldr{\cons(\nil,\nil)}{\varphi}.$$

In Haskell:

> sublists :: (List t) => t a -> t (t a)
> sublists = foldr (cons nil nil) phi
>   where
>     phi a z = cat (map (cons a) z) z

::::::::::::::::::::

Since $\sublists$ is defined as a $\foldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\sublists$ is the unique map $f : \lists{A} \rightarrow \lists{\lists{A}}$ satisfying the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \cons(\nil,\nil) \\
 f(\cons(a,x)) = \cat(\map(\cons(a,-))(f(x)),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_sublists_nil :: (List t, Equal (t (t a)))
>   => t a -> t (t a) -> Test Bool
> _test_sublists_nil t u =
>   testName "sublists(nil) == cons(nil,nil)" $
>   eq
>     (sublists (nil `withTypeOf` t))
>     (cons nil (nil `withTypeOf` u))
> 
> 
> _test_sublists_cons :: (List t, Equal (t (t a)))
>   => t a -> t (t a) -> Test (a -> t a -> Bool)
> _test_sublists_cons _ u =
>   testName "sublists(cons(a,x)) == cat(map(cons(a,-))(x),sublists(x))" $
>   \a x -> eq
>     ((sublists (cons a x)) `withTypeOf` u)
>     (cat (map (cons a) (sublists x)) (sublists x))

::::::::::::::::::::
::::::::::::::::::::

Every item in $\sublists(x)$ is a sublist.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\all(\sublist(-,x))(\sublists(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\nil))(\sublists(\nil)) \\
 & = & \all(\sublist(-,\nil))(\cons(\nil,\nil)) \\
 & = & \band(\sublist(\nil,\nil),\all(\sublist(-,\nil))(\nil)) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $x$ and let $a \in A$. Note that $$\pimpl(\sublist(-,x),\sublist(-,\cons(a,x))),$$ so that $$\bimpl(\all(\sublist(-,x))(z),\all(\sublist(-,\cons(a,x)))(z))$$ for all $z \in \lists{\lists{A}}$. Since $\all(\sublist(-,x))(\sublists(x))$ by the inductive hypothesis, we have $\all(\sublist(-,\cons(a,x)))(\sublists(x)) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)))(\sublists(\cons(a,x))) \\
 & = & \all(\sublist(-,\cons(a,x)))(\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \band(\all(\sublist(-,\cons(a,x)))(\map(\cons(a,-))(\sublists(x))),\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
 & = & \band(\all(\sublist(\cons(a,-),\cons(a,x)))(\sublists(x)),\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
 & = & \band(\all(\sublist(-,x))(\sublists(x)),\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
 & = & \band(\btrue,\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
 & = & \all(\sublist(-,\cons(a,x)))(\sublists(x)) \\
 & = & \btrue
\end{eqnarray*}$$
As needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_sublist :: (List t, Equal a, Equal (t (t a)))
>   => t a -> t (t a) -> Test (t a -> Bool)
> _test_sublists_sublist _ u =
>   testName "all(sublist(-,x))(sublists(x))" $
>   \x -> all (\y -> sublist y x) ((sublists x) `withTypeOf` u)

::::::::::::::::::::
::::::::::::::::::::

$\sublists(x)$ is not $\nil$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\elt(\nil,\sublists(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(\nil,\sublists(\nil)) \\
 & = & \elt(\nil,\cons(\nil,\nil)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \elt(\nil,\sublists(\cons(a,x))) \\
 & = & \elt(\nil,\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \bor(\elt(\nil,\map(\cons(a,-))(\sublists(x))),\elt(\nil,\sublists(x))) \\
 & = & \bor(\elt(\nil,\map(\cons(a,-))(\sublists(x))),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_nil_elt :: (List t, Equal a, Equal (t a))
>   => t a -> t (t a) -> Test (t a -> Bool)
> _test_sublists_nil_elt _ u =
>   testName "elt(nil,sublists(x))" $
>   \x -> elt nil (sublists x)

::::::::::::::::::::
::::::::::::::::::::

Every sublist is an item in $\sublists(x)$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\elt(y,\sublists(x)) = \sublist(y,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(y,\sublists(\nil)) \\
 & = & \elt(y,\cons(\nil,\nil)) \\
 & = & \beq(y,\nil) \\
 & = & \isnil(y) \\
 & = & \sublist(y,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for all $y$ for some $x$, and let $a \in A$. We have two possiblities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(y,\sublists(\cons(a,x))) \\
 & = & \elt(\nil,\sublists(\cons(a,x))) \\
 & = & \btrue \\
 & = & \sublist(\nil,x) \\
 & = & \sublist(y,x)
\end{eqnarray*}$$
as claimed. If $y = \cons(b,w)$, note that $\bimpl(\sublist(\cons(b,w),x),\sublist(w,x))$. Then we have
$$\begin{eqnarray*}
 &   & \elt(y,\sublists(\cons(a,x))) \\
 & = & \elt(y,\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \bor(\elt(y,\map(\cons(a,-))(\sublists(x))),\elt(y,\sublists(x))) \\
 & = & \bor(\elt(y,\map(\cons(a,-))(\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\elt(\cons(b,w),\map(\cons(a,-))(\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\band(\beq(b,a),\elt(w,\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\band(\beq(b,a),\sublist(w,x)),\sublist(y,x)) \\
 &     \href{@or@#thm-or-is-if}
   = & \bif{\band(\beq(b,a),\sublist(w,x))}{\btrue}{\sublist(y,x)} \\
 & = & \bif{\beq(b,a)}{\sublist(w,x)}{\sublist(y,x)} \\
 & = & \bif{\beq(b,a)}{\sublist(w,x)}{\sublist(\cons(b,w),x)} \\
 & = & \sublist(\cons(b,w),\cons(a,x)) \\
 & = & \sublist(y,\cons(a,x))
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_elt_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> t (t a) -> Test (t a -> t a -> Bool)
> _test_sublists_elt_sublist _ u =
>   testName "elt(y,sublists(x)) == sublist(y,x)" $
>   \x y -> eq (elt y (sublists x)) (sublist y x)

::::::::::::::::::::
::::::::::::::::::::

$\sublists$ interacts with $\map$.

:::::: theorem :::::
Let $A$ and $B$ be sets, with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\sublists(\map(f)(x)) = \map(\map(f))(\sublists(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublists(\map(f)(\nil)) \\
 & = & \sublists(\nil) \\
 & = & \cons(\nil,\nil) \\
 & = & \cons(\map(f)(\nil),\map(\map(f))(\nil)) \\
 & = & \map(\map(f))(\cons(\nil,\nil)) \\
 & = & \map(\map(f))(\sublists(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublists(\map(f)(\cons(a,x))) \\
 & = & \sublists(\cons(f(a),\map(f)(x))) \\
 & = & \cat(\map(\cons(f(a),-))(\sublists(\map(f)(x))),\sublists(\map(f)(x))) \\
 & = & \cat(\map(\cons(f(a),-))(\map(\map(f))(\sublists(x))),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\cons(f(a),-) \circ \map(f))(\sublists(x)),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\map(f) \circ \cons(a,-))(\sublists(x)),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\map(f))(\map(\cons(a,-))(\sublists(x))),\map(\map(f))(\sublists(x))) \\
 & = & \map(\map(f))(\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \map(\map(f))(\sublists(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_map :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> t (t a) -> Test ((a -> a) -> t a -> Bool)
> _test_sublists_map _ u =
>   testName "sublists(map(f)(x)) == map(map(f))(sublists(x))" $
>   \f x -> eq (sublists (map f x)) (map (map f) (sublists x))

::::::::::::::::::::
::::::::::::::::::::

$\sublists$ interacts with $\length$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\sublists(x)) = \npower(\next(\next(\zero)),\length(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\sublists(\nil)) \\
 & = & \length(\cons(\nil,\nil)) \\
 & = & \next(\zero) \\
 & = & \npower(\next(\next(\zero)),\zero) \\
 & = & \npower(\next(\next(\zero)),\length(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\sublists(\cons(a,x))) \\
 & = & \length(\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \nplus(\length(\map(\cons(a,-))(\sublists(x))),\length(\sublists(x))) \\
 & = & \nplus(\length(\sublists(x)),\length(\sublists(x))) \\
 &     \href{@times@#thm-times-two}
   = & \ntimes(\next(\next(\zero)),\length(\sublists(x))) \\
 & = & \ntimes(\next(\next(\zero)),\npower(\next(\next(\zero)),\length(x))) \\
 &     \href{@times@#thm-times-commutative}
   = & \ntimes(\npower(\next(\next(\zero)),\length(x)),\next(\next(\zero))) \\
 & = & \npower(\next(\next(\zero)),\next(\length(x))) \\
 & = & \npower(\next(\next(\zero)),\length(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_length :: (List t, Natural n, Equal n)
>   => t a -> n -> Test (t n -> Bool)
> _test_sublists_length _ k =
>   testName "length(sublists(x)) == power(next(next(zero)),length(x))" $
>   \x -> eq
>     ((length (sublists (x))) `withTypeOf` k)
>     (power (next (next zero)) (length x))

::::::::::::::::::::
::::::::::::::::::::

$\select(k)$ is a sublist of $\sublists$.

:::::: theorem :::::
Let $A$ be a set and $k \in \nats$. For all $x \in \lists{A}$ we have $$\sublist(\select(k)(x),\sublists(x)).$$

::: proof ::::::::::
we proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\select(k)(\nil),\sublists(\nil)) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$, and let $a \in A$. We have two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\zero)(\cons(a,x)),\sublists(\cons(a,x))) \\
 & = & \sublist(\cons(\nil,\nil),\sublists(a,x)) \\
 & = & \elt(\nil,\sublists(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose instead that $k = \next(m)$. Now we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(m))(\cons(a,x)),\sublists(\cons(a,x))) \\
 & = & \sublist(\cat(\map(\cons(a,-))(\select(m)(x)),\select(\next(m))(x)),\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & Q.
\end{eqnarray*}$$
By the inductive hypothesis, note that $\cons(a,-)$ is injective, so we have
$$\begin{eqnarray*}
 &   & \sublist(\map(\cons(a,-))(\select(m)(x)),\map(\cons(a,-))(\sublists(x))) \\
 & = & \sublist(\select(m)(x),\sublists(x)) \\
 & = & \btrue,
\end{eqnarray*}$$
and also
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(m))(x),\sublists(x)) \\
 & = & \btrue.
\end{eqnarray*}$$
Since $\sublist$ is compatible with $\cat$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_select :: (List t, Natural n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_sublists_select _ _ =
>   testName "sublist(select(k)(x),sublists(x))" $
>   \k x -> sublist (select k x) (sublists x)

::::::::::::::::::::
::::::::::::::::::::

$\sublists$ interacts with $\filter$.

:::::: theorem :::::
Let $A$ be a set with $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$ we have $$\sublists(\filter(p)(x)) = \filter(\all(p))(\sublists(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \sublists(\filter(p)(\nil)) \\
 & = & \sublists(\nil) \\
 & = & \cons(\nil,\nil) \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\cons(\nil,\nil)}{\filter(\all(p))(\nil)} \\
 & = & \bif{\all(p)(\nil)}{\cons(\nil,\filter(\all(p))(\nil))}{\filter(\all(p))(\nil)} \\
 & = & \filter(\all(p))(\cons(\nil,\nil)) \\
 & = & \filter(\all(p))(\sublists(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for some $x$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \sublists(\filter(p)(\cons(a,x))) \\
 & = & \sublists(\bif{p(a)}{\cons(a,\filter(p)(x))}{\filter(p)(x)}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{p(a)}{\sublists(\cons(a,\filter(p)(x)))}{\sublists(\filter(p)(x))} \\
 & = & \bif{p(a)}{\cat(\map(\cons(a,-))(\sublists(\filter(p)(x))),\sublists(\filter(p)(x)))}{\sublists(\filter(p)(x))} \\
 & = & (@@@)
 & = & \cat(\filter(\all(p))(\map(\cons(a,-))(\sublists(x))),\filter(\all(p))(\sublists(x))) \\
 & = & \filter(\all(p))(\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & \filter(\all(p))(\sublists(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_filter :: (List t, Boolean bool, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> bool -> Test ((a -> Bool) -> t a -> Bool)
> _test_sublists_filter _ _ =
>   testName "sublists(filter(p)(x)) == snoc(nil,filter(any(p))(sublists(x)))" $
>   \p x -> eq
>     (sublists (filter p x))
>     (filter (all p) (sublists x))

::::::::::::::::::::
::::::::::::::::::::

$\sublists$ interacts with $\unique$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\unique(x) = \unique(\sublists(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \unique(\sublists(\nil)) \\
 & = & \unique(\cons(\nil,\nil)) \\
 & = & \btrue \\
 & = & \unique(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \unique(\sublists(\cons(a,x))) \\
 & = & \unique(\cat(\map(\cons(a,-))(\sublists(x)),\sublists(x))) \\
 & = & (@@@) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_unique :: (List t, Boolean bool, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> bool -> Test (t a -> Bool)
> _test_sublists_unique _ _ =
>   testName "unique(sublists(x)) == unique(x)" $
>   \x -> eq
>     (unique (sublists x))
>     (unique x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_sublists ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t (t a))
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   , Boolean bool, Arbitrary bool, CoArbitrary bool
>   , Arbitrary (t n), Show (t n), Equal (t n)
>   ) => t a -> t (t a) -> n -> bool -> Int -> Int -> IO ()
> _test_sublists t u k p maxSize numCases = do
>   testLabel1 "sublists" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_sublists_nil t u)
>   runTest args (_test_sublists_cons t u)
>   runTest args (_test_sublists_sublist t u)
>   runTest args (_test_sublists_nil_elt t u)
>   runTest args (_test_sublists_elt_sublist t u)
>   runTest args (_test_sublists_map t u)
>   runTest args (_test_sublists_length t k)
>   runTest args (_test_sublists_select t k)
>   runTest args (_test_sublists_filter t p)
>   runTest args (_test_sublists_unique t p)

Main:

> main_sublists :: IO ()
> main_sublists = do
>   _test_sublists (nil :: ConsList Bool)  nil (zero :: Unary) (true :: Bool) 10 100
>   _test_sublists (nil :: ConsList Unary) nil (zero :: Unary) (true :: Bool) 10 100
