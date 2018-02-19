---
title: Composition
author: nbloomf
date: 2018-02-18
tags: arithmetic-made-difficult, literate-haskell
slug: compose
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Composition (
>   compose2, _test_compose, main_compose
> ) where
> 
> import Testing
> import Functions
> import Flip

:::::: definition ::
[]{#def-compose2}
We define $$\composeB : (C \rightarrow D \rightarrow E) \rightarrow (A \rightarrow C) \rightarrow (B \rightarrow D) \rightarrow A \rightarrow B \rightarrow E$$ by $$\composeB = \compose(\compose(\compose(\flip)))(\compose(\compose(\compose))(\compose(\compose(\flip))(\compose)))$$

In Haskell:

> compose2 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
> compose2 =
>   compose
>     (compose (compose flip))
>     (compose (compose compose) (compose (compose flip) compose))

::::::::::::::::::::

:::::: theorem :::::
[]{#thm-compose2}
When the signatures of $f$, $g$, and $h$ make sense, we have $$\composeB(f)(g)(h)(x)(y) = f(g(x))(h(y)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \composeB(f)(g)(h)(x)(y) \\
 &     \href{@compose@#def-compose2}
   = & \compose(\compose(\compose(\flip)))(\compose(\compose(\compose))(\compose(\compose(\flip))(\compose)))(f)(g)(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\flip))(\compose(\compose(\compose))(\compose(\compose(\flip))(\compose))(f))(g)(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\flip))(\compose(\compose)(\compose(\compose(\flip))(\compose)(f)))(g)(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\flip))(\compose(\compose)(\compose(\flip)(\compose(f))))(g)(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(\compose(\compose)(\compose(\flip)(\compose(f)))(g))(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(\compose(\compose(\flip)(\compose(f))(g)))(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(\compose(\flip(\compose(f)(g))))(h)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \flip(\compose(\flip(\compose(f)(g)))(h))(x)(y) \\
 &     \href{@flip@#def-flip}
   = & \compose(\flip(\compose(f)(g)))(h)(y)(x) \\
 &     \href{@functions@#def-compose}
   = & \flip(\compose(f)(g))(h(y))(x) \\
 &     \href{@flip@#def-flip}
   = & \compose(f)(g)(x)(h(y)) \\
 &     \href{@functions@#def-compose}
   = & f(g(x))(h(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose2
>   :: (Equal e)
>   => a -> b -> c -> d -> e
>   -> Test ((c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> Bool)
> _test_compose2 _ _ _ _ _ =
>   testName "compose2(f)(g)(h)(x)(y) == f(g(x))(h(y))" $
>   \f g h x y -> eq (compose2 f g h x y) (f (g x) (h y))

::::::::::::::::::::
::::::::::::::::::::

Testing
-------

Suite:

> _test_compose ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a, TypeName a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b, TypeName b
>   , Equal c, Show c, Arbitrary c, CoArbitrary c, TypeName c
>   , Equal d, Show d, Arbitrary d, CoArbitrary d, TypeName d
>   , Equal e, Show e, Arbitrary e, CoArbitrary e, TypeName e
>   ) => Int -> Int -> a -> b -> c -> d -> e -> IO ()
> 
> _test_compose size cases a b c d e = do
>   testLabel0 "compose"
>   let args = testArgs size cases
> 
>   runTest args (_test_compose2 a b c d e)

Main:

> main_compose :: IO ()
> main_compose = do
>   _test_compose 1 1 () () () () ()
