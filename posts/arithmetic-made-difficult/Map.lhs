---
title: Map
author: nbloomf
date: 2017-04-29
tags: arithmetic-made-difficult, literate-haskell
slug: map
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Map
>   ( map, _test_map, main_map
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Functions
> import DisjointUnions
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Cat
> import Length
> import At

Today we'll explore one of the most useful functions on $\lists{A}$: $\map$. What $\map$ does is take a function $A \rightarrow B$ and a $\lists{A}$, and apply the function "itemwise" to get a $\lists{B}$.

:::::: definition ::
Let $A$ and $B$ be sets. Define $\varphi : B^A \rightarrow A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(f)(a,x) = \cons(f(a),x).$$ We then define $\map : B^A \rightarrow \lists{A} \rightarrow \lists{B}$ by $$\map(f) = \foldr{\nil}{\varphi(f)}.$$

In Haskell:

> map :: (List t) => (a -> b) -> t a -> t b
> map f = foldr nil (phi f)
>   where
>     phi g a x = cons (g a) x

::::::::::::::::::::

Since $\map$ is defined as a $\foldr{\ast}{\ast}$, it is the unique solution to a system of functional equations.

:::::: corollary :::
$\map(\alpha)$ is the unique solution $f : \lists{A} \rightarrow \lists{B}$ of the following equations for all $a \in A$ and $x \in \lists{A}$:
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \cons(\alpha(a),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_map_nil :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> Bool)
> _test_map_nil t =
>   testName "map(f)(nil) == nil" $
>   \f -> eq (map f (nil `withTypeOf` t)) nil
> 
> 
> _test_map_cons :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> a -> t a -> Bool)
> _test_map_cons _ =
>   testName "map(f)(cons(a,x)) == cons(f(a),map(f)(x))" $
>   \f a x -> eq (map f (cons a x)) (cons (f a) (map f x))

::::::::::::::::::::
::::::::::::::::::::

One way to think about $\map$ is that it fills in the following diagram.
$$\require{AMScd}
\begin{CD}
A @>{f}>> B\\
@V{\lists{\ast}}VV @VV{\lists{\ast}}V \\
\lists{A} @>>{\map(f)}> \lists{B}
\end{CD}$$
This looks an awful lot like a functor diagram. Recall that given two categories, a functor associates objects to objects and morphisms to morphisms, preserving $\id$ and composition. And indeed, $\map$ is the morphism part of the $\lists{\ast}$ functor.

$\map$ takes $\id_A$ to $\id_{\lists{A}}$.

:::::: theorem :::::
Let $A$ be a set. Then we have $$\map(\id_A)(x) = x.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\id)(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(\id)(\cons(a,x)) \\
 & = & \cons(\id(a),\map(\id)(x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_id :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_map_id _ =
>   testName "map(id)(x) == x" $
>   \x -> eq (map id x) x

::::::::::::::::::::
::::::::::::::::::::

$\map$ preserves composition.

:::::: theorem :::::
Let $A$, $B$, and $C$ be sets, with maps $f : A \rightarrow B$ and $g : B \rightarrow C$. For all $x \in \lists{A}$ we have $$\map(g \circ f)(x) = (\map(g) \circ \map(f))(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(x) \\
 & = & (\map(g) \circ \map(f))(\nil) \\
 & = & \map(g)(\map(f)(\nil)) \\
 & = & \map(g)(\nil) \\
 & = & \nil \\
 & = & \map(g \circ f)(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(\cons(a,x)) \\
 & = & \map(g)(\map(f)(\cons(a,x))) \\
 & = & \map(g)(\cons(f(a),\map(f)(x))) \\
 & = & \cons(g(f(a)),\map(g)(\map(f)(x))) \\
 & = & \cons((g \circ f)(a),(\map(g) \circ \map(f))(x)) \\
 & = & \cons((g \circ f)(a),\map(g \circ f)(x)) \\
 & = & \map(g \circ f)(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_compose :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> (a -> a) -> t a -> Bool)
> _test_map_compose _ =
>   testName "map(g . f)(x) == (map(g) . map(f))(x)" $
>   \g f x -> eq (map (g . f) x) (((map g) . (map f)) x)

::::::::::::::::::::
::::::::::::::::::::

$\map(f)$ respects $\tail$.

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\tail(x)) = \tail(\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\nil)) \\
 &     \href{@head-tail@#thm-tail-nil}
   = & \map(f)(\nil) \\
 & = & \nil \\
 &     \href{@head-tail@#thm-tail-nil}
   = & \tail(\nil) \\
 & = & \tail(\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\cons(a,x))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \map(f)(x) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \tail(\cons(f(a),\map(f)(x))) \\
 & = & \tail(\map(f)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_tail :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_map_tail _ =
>   testName "map(f)(tail(x)) == tail(map(f)(x))" $
>   \f x -> eq (map f (tail x)) (tail (map f x))

::::::::::::::::::::
::::::::::::::::::::

$\map(f)$ respects $\cat$.

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x,y \in \lists{A}$, we have $$\map(f)(\cat(x,y)) = \cat(\map(f)(x),\map(f)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\cat(x,y)) \\
 & = & \map(f)(\cat(\nil,y)) \\
 &     \href{@cat@#cor-cat-nil}
   = & \map(f)(y) \\
 &     \href{@cat@#cor-cat-nil}
   = & \cat(\nil,\map(f)(y)) \\
 & = & \cat(\map(f)(\nil),\map(f)(y)) \\
 & = & \cat(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\cat(\cons(a,x),y)) \\
 &     \href{@cat@#cor-cat-cons}
   = & \map(f)(\cons(a,\cat(x,y))) \\
 & = & \cons(f(a),\map(f)(\cat(x,y))) \\
 & = & \cons(f(a),\cat(\map(f)(x),\map(f)(y))) \\
 &     \href{@cat@#cor-cat-cons}
   = & \cat(\cons(f(a),\map(f)(x)),\map(f)(y)) \\
 & = & \cat(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_cat :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> t a -> Bool)
> _test_map_cat _ =
>   testName "map(f)(cat(x,y)) == cat(map(f)(x),map(f)(y))" $
>   \f x y -> eq (map f (cat x y)) (cat (map f x) (map f y))

::::::::::::::::::::
::::::::::::::::::::

$\map(f)$ respects $\snoc$.

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $a \in A$ and $x \in \lists{A}$, we have $$\map(f)(\snoc(a,x)) = \snoc(f(a),\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \map(f)(\cons(a,\nil)) \\
 & = & \cons(f(a),\map(f)(\nil)) \\
 & = & \cons(f(a),\nil) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \snoc(f(a),\nil) \\
 & = & \snoc(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ and $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \map(f)(\cons(b,\snoc(a,x))) \\
 & = & \cons(f(b),\map(f)(\snoc(a,x))) \\
 & = & \cons(f(b),\snoc(f(a),\map(f)(x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \snoc(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_snoc :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> a -> t a -> Bool)
> _test_map_snoc _ =
>   testName "map(f)(snoc(a,x)) == snoc(f(a),map(f)(x))" $
>   \f a x -> eq (map f (snoc a x)) (snoc (f a) (map f x))

::::::::::::::::::::
::::::::::::::::::::

$\map(f)$ respects $\rev$.

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\rev(x)) = \rev(\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\rev(x)) \\
 & = & \map(f)(\rev(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \map(f)(\nil) \\
 & = & \nil \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\nil) \\
 & = & \rev(\map(f)(\nil)) \\
 & = & \rev(\map(f)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\rev(\cons(a,x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \map(f)(\snoc(a,\rev(x))) \\
 & = & \snoc(f(a),\map(f)(\rev(x))) \\
 & = & \snoc(f(a),\rev(\map(f)(x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \rev(\cons(f(a),\map(f)(x))) \\
 & = & \rev(\map(f)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_rev :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_map_rev _ =
>   testName "map(f)(rev(x)) == rev(map(f)(x))" $
>   \f x -> eq (map f (rev x)) (rev (map f x))

::::::::::::::::::::
::::::::::::::::::::

$\map(f)$ interacts with $\at$:

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$ and $x \in \lists{A}$. Then we have $$\at(\map(f)(x),k) = \uPair(\id,f)(\at(x,k)).$$

::: proof ::::::::::
There are two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\nil),k) \\
 & = & \at(\nil,k) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast) \\
 &     \href{@functions@#def-id}
   = & \lft(\id(\ast)) \\
 & = & \uPair(\id,f)(\lft(\ast)) \\
 &     \href{@at@#thm-at-nil}
   = & \uPair(\id,f)(\at(\nil,k))
\end{eqnarray*}$$
as claimed. Suppose instead that $x = \cons(a,y)$. We now proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\zero) \\
 & = & \at(\cons(f(a),\map(f)(y)),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(f(a)) \\
 &     \href{@disjoint-unions@#thm-uPair-rgt}
   = & \uPair(\id,f)(\rgt(a)) \\
 & = & \uPair(\id,f)(\at(\cons(a,y),\zero))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $y$ for some $k$. Now
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\next(k)) \\
 & = & \at(\cons(f(a),\map(f)(y)),\next(k)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\map(f)(y),k) \\
 & = & \uPair(\id,f)(\at(y,k)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \uPair(\id,f)(\at(\cons(a,y),\next(k)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_at :: (List t, Equal (t a), Natural n, Equal n, Equal a)
>   => t a -> n -> Test ((a -> a) -> t a -> n -> Bool)
> _test_map_at _ _ =
>   testName "at(map(f)(x),k) == upair(id,f)(at(x,k))" $
>   \f x k -> eq (at (map f x) k) (upair id f (at x k))

::::::::::::::::::::
::::::::::::::::::::

And $\map$ preserves $\length$.

:::::: theorem :::::
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. Then for all $x \in \lists{A}$ we have $$\length(\map(f)(x)) = \length(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \length(\map(f)(x)) \\
 & = & \length(\map(f)(\nil)) \\
 & = & \length(\nil) \\
 & = & \length(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\map(f)(\cons(a,x))) \\
 & = & \length(\cons(f(a),\map(f)(x))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\map(f)(x))) \\
 & = & \next(\length(x)) \\
 &     \href{@length@#cor-length-cons}
   = & \length(\cons(a,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_length :: (List t, Equal (t a), Natural n, Equal n, Equal a)
>   => t a -> n -> Test ((a -> a) -> t a -> Bool)
> _test_map_length _ k =
>   testName "length(map(f)(x)) == length(x)" $
>   \f x -> eq (length (map f x)) ((length x) `withTypeOf` k)

::::::::::::::::::::
::::::::::::::::::::

$\map$ preserves $\isnil$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\isnil(\map(f)(x)) = \isnil(x).$$

::: proof ::::::::::
We have two possibilities for $x$. If $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \isnil(\map(f)(\nil)) \\
 & = & \isnil(\nil)
\end{eqnarray*}$$
and if $x = \cons(a,u)$ we have
$$\begin{eqnarray*}
 &   & \isnil(\map(f)(\cons(a,u))) \\
 & = & \isnil(\cons(f(a),\map(f)(u))) \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \bfalse \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \isnil(\cons(a,u))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_map_isnil :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_map_isnil _ =
>   testName "isnil(map(f)(x)) == isnil(x)" $
>   \f x -> eq (isNil (map f x)) (isNil x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_map ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   , TypeName n, Show n, Equal n, Natural n, Arbitrary n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_map t n maxSize numCases = do
>   testLabel1 "map" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_map_nil t)
>   runTest args (_test_map_cons t)
>   runTest args (_test_map_id t)
>   runTest args (_test_map_compose t)
>   runTest args (_test_map_tail t)
>   runTest args (_test_map_cat t)
>   runTest args (_test_map_snoc t)
>   runTest args (_test_map_rev t)
>   runTest args (_test_map_at t n)
>   runTest args (_test_map_length t n)
>   runTest args (_test_map_isnil t)

Main:

> main_map :: IO ()
> main_map = do
>   _test_map (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_map (nil :: ConsList Unary) (zero :: Unary) 20 100
