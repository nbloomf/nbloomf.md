---
title: Composition
author: nbloomf
date: 2018-02-18
tags: arithmetic-made-difficult, literate-haskell
slug: compose
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Composition (
>   compose2, compose3, _test_compose, main_compose
> ) where
> 
> import Testing
> import Functions
> import Flip

(@@@)

:::::: definition ::
[]{#def-compose2}
We define $$\composeB : (C \rightarrow D \rightarrow E) \rightarrow (A \rightarrow C) \rightarrow (B \rightarrow D) \rightarrow A \rightarrow B \rightarrow E$$ by $$\composeB = \flipC(\compose(\compose(\compose(\compose)))(\compose))$$

In Haskell:

> compose2 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
> compose2 = flip3 (compose (compose (compose compose)) compose)

::::::::::::::::::::

(@@@)

:::::: theorem :::::
[]{#thm-compose2}
When the signatures of $f$, $g$, and $h$ make sense, we have $$\composeB(f)(g)(h)(x)(y) = f(g(x))(h(y)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \composeB(f)(g)(h)(x)(y) \\
 &     \href{@compose@#def-compose2}
   = & \flipC(\compose(\compose(\compose(\compose)))(\compose))(f)(g)(h)(x)(y) \\
 &     \href{@flip@#thm-flip3}
   = & \compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose))(\compose(f))(g)(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose)(\compose(f)(g))(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(f)(g)(x))(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(f(g(x)))(h)(y) \\
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

(@@@)

:::::: definition ::
[]{#def-compose3}
We define
$$\begin{eqnarray*}
\composeC
  & : & (D \rightarrow E \rightarrow F \rightarrow G) \\
  &   & \rightarrow (A \rightarrow D) \\
  &   & \rightarrow (B \rightarrow E) \\
  &   & \rightarrow (C \rightarrow F) \\
  &   & \rightarrow A \rightarrow B \rightarrow C \rightarrow G
\end{eqnarray*}$$
by $$\composeC = \flipD(\flipE(\flipC(\compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose)))))$$

In Haskell:

> compose3
>   :: (d -> e -> f -> g)
>   -> (a -> d)
>   -> (b -> e)
>   -> (c -> f)
>   -> a -> b -> c -> g
> 
> compose3 =
>   flip4 (flip5 (flip3 (
>     compose
>       (compose (compose (compose (compose compose))))
>       (compose
>         (compose (compose compose))
>         (compose))
>   )))

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
