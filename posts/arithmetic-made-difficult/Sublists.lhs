---
title: Sublists
author: nbloomf
date: 2018-01-20
tags: arithmetic-made-difficult, literate-haskell
slug: sublists
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Sublists
>   ( sublists, _test_sublists, main_sublists
>   ) where
> 
> import Testing
> import Booleans
> import Unary
> import NaturalNumbers
> import Exponentiation
> import Lists
> import Cat
> import Length
> import Map
> import AllAndAny
> import Elt
> import Sublist
> import Select

We've already defined a predicate that detects when one list is a sublist of another. Today we'll define a function that constructs a list of all sublists of a given list.

:::::: definition ::
Let $A$ be a set. Define $\varphi : A \times \lists{\lists{A}} \rightarrow \lists{\lists{A}}$ by $$\varphi(a,z) = \cat(\map(\cons(a)(z)),z).$$ Now define $\sublists : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\sublists = \foldr(\cons(\nil,\nil))(\varphi).$$

In Haskell:

> sublists :: (List t) => t a -> t (t a)
> sublists = foldr (cons nil nil) phi
>   where
>     phi a z = cat (map (cons a) z) z

::::::::::::::::::::

Since $\sublists$ is defined as a $\foldr(\ast)(\ast)$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\sublists$ is the unique map $f : \lists{A} \rightarrow \lists{\lists{A}}$ satisfying the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \cons(\nil,\nil) \\
 f(\cons(a,x)) = \cat(\map(\cons(a))(f(x)),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_sublists_nil :: (List t, Equal (t (t a)))
>   => t a -> Test Bool
> _test_sublists_nil t =
>   testName "sublists(nil) == cons(nil,nil)" $
>   eq
>     (sublists (nil `withTypeOf` t))
>     (cons nil nil)
> 
> 
> _test_sublists_cons :: (List t, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_sublists_cons _ =
>   testName "sublists(cons(a,x)) == cat(map(cons(a,-))(x),sublists(x))" $
>   \a x -> eq
>     (sublists (cons a x))
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
 & = & \all(\sublist(-,\cons(a,x)))(\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
 & = & \band(\all(\sublist(-,\cons(a,x)))(\map(\cons(a))(\sublists(x))),\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
 & = & \band(\all(\sublist(\cons(a),\cons(a,x)))(\sublists(x)),\all(\sublist(-,\cons(a,x)))(\sublists(x))) \\
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
 & = & \elt(\nil,\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
 & = & \bor(\elt(\nil,\map(\cons(a))(\sublists(x))),\elt(\nil,\sublists(x))) \\
 & = & \bor(\elt(\nil,\map(\cons(a))(\sublists(x))),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_sublists_nil_elt :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_sublists_nil_elt _ =
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
 &     \href{@sublist@#cor-sublist-nil}
   = & \sublist(y,\nil)
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
 & = & \elt(y,\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
 & = & \bor(\elt(y,\map(\cons(a))(\sublists(x))),\elt(y,\sublists(x))) \\
 & = & \bor(\elt(y,\map(\cons(a))(\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\elt(\cons(b,w),\map(\cons(a))(\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\band(\beq(b,a),\elt(w,\sublists(x))),\sublist(y,x)) \\
 & = & \bor(\band(\beq(b,a),\sublist(w,x)),\sublist(y,x)) \\
 &     \href{@or@#thm-or-is-if}
   = & \bif{\band(\beq(b,a),\sublist(w,x))}{\btrue}{\sublist(y,x)} \\
 & = & \bif{\beq(b,a)}{\sublist(w,x)}{\sublist(y,x)} \\
 & = & \bif{\beq(b,a)}{\sublist(w,x)}{\sublist(\cons(b,w),x)} \\
 &     \href{@sublist@#cor-sublist-cons-cons}
   = & \sublist(\cons(b,w),\cons(a,x)) \\
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
 &     \href{@map@#cor-map-nil}
   = & \sublists(\nil) \\
 & = & \cons(\nil,\nil) \\
 & = & \cons(\map(f)(\nil),\map(\map(f))(\nil)) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\map(f))(\cons(\nil,\nil)) \\
 & = & \map(\map(f))(\sublists(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublists(\map(f)(\cons(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \sublists(\cons(f(a),\map(f)(x))) \\
 & = & \cat(\map(\cons(f(a),-))(\sublists(\map(f)(x))),\sublists(\map(f)(x))) \\
 & = & \cat(\map(\cons(f(a),-))(\map(\map(f))(\sublists(x))),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\cons(f(a),-) \circ \map(f))(\sublists(x)),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\map(f) \circ \cons(a))(\sublists(x)),\map(\map(f))(\sublists(x))) \\
 & = & \cat(\map(\map(f))(\map(\cons(a))(\sublists(x))),\map(\map(f))(\sublists(x))) \\
 &     \href{@map@#thm-map-cat}
   = & \map(\map(f))(\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
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
 &     \href{@length@#thm-length-singleton}
   = & \next(\zero) \\
 & = & \npower(\next(\next(\zero)),\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \npower(\next(\next(\zero)),\length(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\sublists(\cons(a,x))) \\
 & = & \length(\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
 &     \href{@length@#thm-length-cat}
   = & \nplus(\length(\map(\cons(a))(\sublists(x))),\length(\sublists(x))) \\
 &     \href{@map@#thm-length-map}
   = & \nplus(\length(\sublists(x)),\length(\sublists(x))) \\
 &     \href{@times@#thm-times-two}
   = & \ntimes(\next(\next(\zero)),\length(\sublists(x))) \\
 & = & \ntimes(\next(\next(\zero)),\npower(\next(\next(\zero)),\length(x))) \\
 &     \href{@times@#thm-times-commutative}
   = & \ntimes(\npower(\next(\next(\zero)),\length(x)),\next(\next(\zero))) \\
 & = & \npower(\next(\next(\zero)),\next(\length(x))) \\
 &     \href{@length@#cor-length-cons}
   = & \npower(\next(\next(\zero)),\length(\cons(a,x)))
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
 &     \href{@sublist@#thm-sublist-reflexive}
   = & \btrue
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
 & = & \sublist(\cat(\map(\cons(a))(\select(m)(x)),\select(\next(m))(x)),\cat(\map(\cons(a))(\sublists(x)),\sublists(x))) \\
 & = & Q.
\end{eqnarray*}$$
By the inductive hypothesis, note that $\cons(a)$ is injective, so we have
$$\begin{eqnarray*}
 &   & \sublist(\map(\cons(a))(\select(m)(x)),\map(\cons(a))(\sublists(x))) \\
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


Testing
-------

Suite:

> _test_sublists ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a, TypeName a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b, TypeName b, Boolean b
>   , Equal n, Show n, Arbitrary n, CoArbitrary n, TypeName n, Natural n
>   , Equal (t a), Show (t a), Arbitrary (t a), CoArbitrary (t a), TypeName (t a), List t
>   , Equal (t n), Show (t n), Arbitrary (t n), CoArbitrary (t n), TypeName (t n)
>   , Equal (t (t a))
>   ) => Int -> Int -> t a -> t (t a) -> n -> b -> IO ()
> _test_sublists size cases t u k p = do
>   testLabel1 "sublists" t
>   let args = testArgs size cases
> 
>   runTest args (_test_sublists_nil t)
>   runTest args (_test_sublists_cons t)
>   runTest args (_test_sublists_sublist t u)
>   runTest args (_test_sublists_nil_elt t)
>   runTest args (_test_sublists_elt_sublist t u)
>   runTest args (_test_sublists_map t u)
>   runTest args (_test_sublists_length t k)
>   runTest args (_test_sublists_select t k)

Main:

> main_sublists :: IO ()
> main_sublists = do
>   _test_sublists 10 100 (nil :: ConsList Bool)  nil (zero :: Unary) (true :: Bool)
>   _test_sublists 10 100 (nil :: ConsList Unary) nil (zero :: Unary) (true :: Bool)
