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
> import Lists
> import Map
> import Cat

(@@@)

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

(@@@)


Testing
-------

Suite:

> _test_sublists ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t (t a))
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   , Arbitrary (t n), Show (t n), Equal (t n)
>   ) => t a -> t (t a) -> n -> Int -> Int -> IO ()
> _test_sublists t u k maxSize numCases = do
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

Main:

> main_sublists :: IO ()
> main_sublists = do
>   _test_sublists (nil :: ConsList Bool)  nil (zero :: Unary) 10 100
>   _test_sublists (nil :: ConsList Unary) nil (zero :: Unary) 10 100
