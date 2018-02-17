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
[]{#def-map}
Let $A$ and $B$ be sets. We then define $\map : B^A \rightarrow \lists{A} \rightarrow \lists{B}$ by $$\map(f) = \foldr{\nil}{\compose(\cons)(f)}.$$

In Haskell:

> map :: (List t) => (a -> b) -> t a -> t b
> map f = foldr nil (compose cons f)

::::::::::::::::::::

Since $\map$ is defined as a $\foldr{\ast}{\ast}$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-map-nil}[]{#cor-map-cons}
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
[]{#thm-map-id}
Let $A$ be a set. Then we have $$\map(\id_A)(x) = x.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\id)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(\id)(\cons(a,x)) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(\id(a),\map(\id)(x)) \\
 &     \hyp{\map(\id)(x) = x}
   = & \cons(\id(a),x) \\
 &     \href{@functions@#def-id}
   = & \cons(a,x)
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
[]{#thm-map-compose}
Let $A$, $B$, and $C$ be sets, with maps $f : A \rightarrow B$ and $g : B \rightarrow C$. For all $x \in \lists{A}$ we have $$\map(\compose(g)(f))(x) = \compose(\map(g))(\map(f))(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \compose(\map(g))(\map(f))(\nil) \\
 &     \href{@functions@#def-compose}
   = & \map(g)(\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \map(g)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\compose(g)(f))(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \compose(\map(g))(\map(f))(\cons(a,x)) \\
 &     \href{@functions@#def-compose}
   = & \map(g)(\map(f)(\cons(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \map(g)(\cons(f(a),\map(f)(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(g(f(a)),\map(g)(\map(f)(x))) \\
 &     \href{@functions@#def-compose}
   = & \cons(\compose(g)(f)(a),\map(g)(\map(f)(x))) \\
 &     \href{@functions@#def-compose}
   = & \cons(\compose(g)(f)(a),\compose(\map(g))(\map(f))(x)) \\
 &     \href{@map@#thm-map-compose}
   = & \cons(\compose(g)(f)(a),\map(\compose(g)(f))(x)) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\compose(g)(f))(\cons(a,x))
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
[]{#thm-map-tail}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\tail(x)) = \tail(\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\nil)) \\
 &     \href{@head-tail@#thm-tail-nil}
   = & \map(f)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@head-tail@#thm-tail-nil}
   = & \tail(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \tail(\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\cons(a,x))) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \map(f)(x) \\
 &     \href{@head-tail@#thm-tail-cons}
   = & \tail(\cons(f(a),\map(f)(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \tail(\map(f)(\cons(a,x)))
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
[]{#thm-map-cat}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x,y \in \lists{A}$, we have $$\map(f)(\cat(x,y)) = \cat(\map(f)(x),\map(f)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\cat(\nil,y)) \\
 &     \href{@cat@#cor-cat-nil}
   = & \map(f)(y) \\
 &     \href{@cat@#cor-cat-nil}
   = & \cat(\nil,\map(f)(y)) \\
 &     \href{@map@#cor-map-nil}
   = & \cat(\map(f)(\nil),\map(f)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\cat(\cons(a,x),y)) \\
 &     \href{@cat@#cor-cat-cons}
   = & \map(f)(\cons(a,\cat(x,y))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(f(a),\map(f)(\cat(x,y))) \\
 &     \href{@map@#thm-map-cat}
   = & \cons(f(a),\cat(\map(f)(x),\map(f)(y))) \\
 &     \href{@cat@#cor-cat-cons}
   = & \cat(\cons(f(a),\map(f)(x)),\map(f)(y)) \\
 &     \href{@map@#cor-map-cons}
   = & \cat(\map(f)(\cons(a,x)),\map(f)(y))
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
[]{#thm-map-snoc}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $a \in A$ and $x \in \lists{A}$, we have $$\map(f)(\snoc(a,x)) = \snoc(f(a),\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \map(f)(\cons(a,\nil)) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(f(a),\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \cons(f(a),\nil) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \snoc(f(a),\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \snoc(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ and $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \map(f)(\cons(b,\snoc(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(f(b),\map(f)(\snoc(a,x))) \\
 &     \hyp{\map(f)(\snoc(a,x)) = \snoc(f(a),\map(f)(x))}
   = & \cons(f(b),\snoc(f(a),\map(f)(x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(f(a),\cons(f(b),\map(f)(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \snoc(f(a),\map(f)(\cons(b,x)))
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
[]{#thm-map-rev}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\rev(x)) = \rev(\map(f)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\rev(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \map(f)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \rev(\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\rev(\cons(a,x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \map(f)(\snoc(a,\rev(x))) \\
 &     \href{@map@#thm-map-snoc}
   = & \snoc(f(a),\map(f)(\rev(x))) \\
 &     \hyp{\map(f)(\rev(x)) = \rev(\map(f)(x))}
   = & \snoc(f(a),\rev(\map(f)(x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \rev(\cons(f(a),\map(f)(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \rev(\map(f)(\cons(a,x)))
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
[]{#thm-at-map}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$ and $x \in \lists{A}$. Then we have $$\at(\map(f)(x),k) = \uPair(\id,f)(\at(x,k)).$$

::: proof ::::::::::
There are two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\nil),k) \\
 &     \href{@map@#cor-map-nil}
   = & \at(\nil,k) \\
 &     \href{@at@#thm-at-nil}
   = & \lft(\ast) \\
 &     \href{@functions@#def-id}
   = & \lft(\id(\ast)) \\
 &     \href{@disjoint-unions@#thm-uPair-lft}
   = & \uPair(\id,f)(\lft(\ast)) \\
 &     \href{@at@#thm-at-nil}
   = & \uPair(\id,f)(\at(\nil,k))
\end{eqnarray*}$$
as claimed. Suppose instead that $x = \cons(a,y)$. We now proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\zero) \\
 &     \href{@map@#cor-map-cons}
   = & \at(\cons(f(a),\map(f)(y)),\zero) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \rgt(f(a)) \\
 &     \href{@disjoint-unions@#thm-uPair-rgt}
   = & \uPair(\id,f)(\rgt(a)) \\
 &     \href{@at@#thm-at-cons-zero}
   = & \uPair(\id,f)(\at(\cons(a,y),\zero))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $y$ for some $k$. Now
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\next(k)) \\
 &     \href{@map@#cor-map-cons}
   = & \at(\cons(f(a),\map(f)(y)),\next(k)) \\
 &     \href{@at@#thm-at-cons-next}
   = & \at(\map(f)(y),k) \\
 &     \hyp{\at(\map(f)(x),k) = \uPair(\id,f)(\at(y,k))}
   = & \uPair(\id,f)(\at(y,k)) \\
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
[]{#thm-length-map}
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. Then for all $x \in \lists{A}$ we have $$\length(\map(f)(x)) = \length(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \length(\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \length(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\map(f)(\cons(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \length(\cons(f(a),\map(f)(x))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\map(f)(x))) \\
 &     \hyp{\length(\map(f)(x)) = \length(x)}
   = & \next(\length(x)) \\
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
[]{#thm-isnil-map}
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\isnil(\map(f)(x)) = \isnil(x).$$

::: proof ::::::::::
We have two possibilities for $x$. If $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \isnil(\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \isnil(\nil)
\end{eqnarray*}$$
and if $x = \cons(a,u)$ we have
$$\begin{eqnarray*}
 &   & \isnil(\map(f)(\cons(a,u))) \\
 &     \href{@map@#cor-map-cons}
   = & \isnil(\cons(f(a),\map(f)(u))) \\
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
> _test_map t n size cases = do
>   testLabel1 "map" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = cases
>       , maxSize    = size
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
