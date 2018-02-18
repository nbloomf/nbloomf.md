---
title: Clone
author: nbloomf
date: 2018-02-17
tags: arithmetic-made-difficult, literate-haskell
slug: clone
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Clone (
>   clone, _test_clone, main_clone
> ) where
> 
> import Testing
> import Functions
> import Flip

Today we'll define some operators for repeating function arguments. These will be handy for defining functions that need to "consume" their input more than once.

:::::: definition ::
[]{#def-clone}
Let $A$ and $B$ be sets. We define $$\clone : (A \rightarrow A \rightarrow B) \rightarrow A \rightarrow B$$ by $$\clone(f)(x) = f(x)(x).$$

In Haskell:

> clone :: (a -> a -> b) -> a -> b
> clone f a = f a a

::::::::::::::::::::

$\clone$ interacts with $\flip$.

:::::: theorem :::::
[]{#thm-clone-flip}
Let $A$ and $B$ be sets, with $f : A \rightarrow A \rightarrow B$. Then we have $$\clone(\flip(f)) = \clone(f).$$

::: proof ::::::::::
Let $x \in A$. Then we have
$$\begin{eqnarray*}
 &   & \clone(\flip(f))(x) \\
 &     \href{@clone@#def-clone}
   = & \flip(f)(x)(x) \\
 &     \href{@flip@#def-flip}
   = & f(x)(x) \\
 &     \href{@clone@#def-clone}
   = & \clone(f)(x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_clone_flip
>   :: (Equal b)
>   => a -> b
>   -> Test ((a -> a -> b) -> a -> Bool)
> _test_clone_flip _ _ =
>   testName "clone(flip(f)) == clone(f)" $
>   \f a -> eq (clone (flip f) a) (clone f a)

::::::::::::::::::::
::::::::::::::::::::

The same, but moreso.

:::::: definition ::
[]{#def-clone3}
Let $A$ and $B$ be sets. We define $$\cloneC : (A \rightarrow A \rightarrow A \rightarrow B) \rightarrow A \rightarrow B$$ by $$\cloneC = \compose(\clone)(\compose(\clone)).$$

In Haskell:

> clone3 :: (a -> a -> a -> b) -> a -> b
> clone3 = compose clone (compose clone)

::::::::::::::::::::

$\cloneC$ does what we expect:

:::::: theorem :::::
[]{#thm-clone3}
Let $A$ and $B$ be sets. For all $f : A \rightarrow A \rightarrow A \rightarrow B$ and all $x \in A$, we have $$\cloneC(f)(x) = f(x)(x)(x).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \cloneC(f)(x) \\
 &     \href{@clone@#def-clone3}
   = & \compose(\clone)(\compose(\clone))(f)(x) \\
 &     \href{@functions@#def-compose}
   = & \clone(\compose(\clone)(f))(x) \\
 &     \href{@clone@#def-clone}
   = & \compose(\clone)(f)(x)(x) \\
 &     \href{@functions@#def-compose}
   = & \clone(f(x))(x) \\
 &     \href{@clone@#def-clone}
   = & f(x)(x)(x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_clone3
>   :: (Equal b)
>   => a -> b
>   -> Test ((a -> a -> a -> b) -> a -> Bool)
> _test_clone3 _ _ =
>   testName "clone3(f)(x) == f(x)(x)(x)" $
>   \f a -> eq (clone3 f a) (f a a a)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_clone ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b
>   ) => Int -> Int -> a -> b -> IO ()
> _test_clone size cases a b = do
>   testLabel0 "clone"
>   let args = testArgs size cases
> 
>   runTest args (_test_clone_flip a b)
>   runTest args (_test_clone3 a b)

Main:

> main_clone :: IO ()
> main_clone = do
>   _test_clone 1 1 () ()
