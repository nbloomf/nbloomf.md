---
title: Functions
author: nbloomf
date: 2018-01-30
tags: arithmetic-made-difficult, literate-haskell
slug: functions
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Functions (
>   id, compose, const, flip, apply, _test_functions, main_functions
> ) where
> 
> import Testing

Today we'll nail down some generic functions.

Every set has an associated _identity_ function.

:::::: definition ::
[]{#def-id}
Let $A$ be a set. We define $\id : A \rightarrow A$ by $\id(x) = x$.

In Haskell:

> id :: a -> a
> id a = a

::::::::::::::::::::

Given two functions, one with domain $B$ and the other with codomain $B$, we can construct their _composite_.

:::::: definition ::
[]{#def-compose}
Let $A$, $B$, and $C$ be sets. Given $f : A \rightarrow B$ and $B : B \rightarrow C$, we define $\compose(g)(f) : A \rightarrow C$ by $$\compose(g)(f)(x) = g(f(x)).$$

In Haskell:

> compose :: (b -> c) -> (a -> b) -> a -> c
> compose g f x = g (f x)

::::::::::::::::::::

$\id$ is neutral under $\compose(\ast)(\ast)$.

:::::: theorem :::::
[]{#thm-compose-id}[]{#thm-compose-id-left}[]{#thm-compose-id-right}
Let $A$ and $B$ be sets, with $f : A \rightarrow B$. Then we have the following.

1. $\compose(\id)(f) = f$.
2. $\compose(f)(\id) = f$.

::: proof ::::::::::
1. Let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \compose(\id)(f)(a) \\
 &     \href{@functions@#def-compose}
   = & \id(f(a)) \\
 &     \href{@functions@#def-id}
   = & f(a)
\end{eqnarray*}$$
as needed.
2. Let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \compose(f)(\id)(a) \\
 &     \href{@functions@#def-compose}
   = & f(\id(a)) \\
 &     \href{@functions@#def-id}
   = & f(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose_id_left :: (Equal b)
>   => a -> b -> Test ((a -> b) -> a -> Bool)
> _test_compose_id_left _ _ =
>   testName "compose(id)(f) == f" $
>   \f a -> eq (compose id f a) (f a)
> 
> _test_compose_id_right :: (Equal b)
>   => a -> b -> Test ((a -> b) -> a -> Bool)
> _test_compose_id_right _ _ =
>   testName "compose(f)(id) == f" $
>   \f a -> eq (compose f id a) (f a)

::::::::::::::::::::
::::::::::::::::::::

$\compose(\ast)(\ast)$ is associative.

:::::: theorem :::::
[]{#thm-compose-associative}
Let $A$, $B$, $C$, and $D$ be sets. For all $f : A \rightarrow B$, $g : B \rightarrow C$, and $h : C \rightarrow D$, we have $$\compose(h)(\compose(g)(f)) = \compose(\compose(h)(g))(f).$$

::: proof ::::::::::
Let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \compose(h)(\compose(g)(f))(a) \\
 &     \href{@functions@#def-compose}
   = & h(\compose(g)(f)(a)) \\
 &     \href{@functions@#def-compose}
   = & h(g(f(a))) \\
 &     \href{@functions@#def-compose}
   = & \compose(h)(g)(f(a)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(h)(g))(f)(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose_associative :: (Equal d)
>   => a -> b -> c -> d -> Test ((c -> d) -> (b -> c) -> (a -> b) -> a -> Bool)
> _test_compose_associative _ _ _ _ =
>   testName "compose(h)(compose(g)(f)) == compose(compose(h)(g))(f)" $
>   \h g f a -> eq
>     (compose h (compose g f) a)
>     (compose (compose h g) f a)

::::::::::::::::::::
::::::::::::::::::::

The $\const$ function throws away its second argument.

:::::: definition ::
[]{#def-const}
Let $A$ and $B$ be sets. We define $\const : B \rightarrow B^A$ by $$\const(b)(a) = b.$$

In Haskell:

> const :: b -> a -> b
> const b _ = b

::::::::::::::::::::

$\const(b)$ absorbs under $\compose(\ast)(\ast)$ from the left.

:::::: theorem :::::
[]{#thm-compose-const-left}
Let $A$, $B$, and $C$ be sets. For all $f : A \rightarrow B$ and $c \in C$ we have $$\compose(\const(c))(f) = \const(c).$$

::: proof ::::::::::
Let $a \in A$. Note that
$$\begin{eqnarray*}
 &   & \compose(\const(c))(f)(a) \\
 &     \href{@functions@#def-compose}
   = & \const(c)(f(a)) \\
 &     \href{@functions@#def-const}
   = & c \\
 &     \href{@functions@#def-const}
   = & \const(c)(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose_const_left :: (Equal c)
>   => a -> b -> c -> Test (c -> (a -> b) -> a -> Bool)
> _test_compose_const_left _ _ _ =
>   testName "compose(const(c))(f) == const(c)" $
>   \c f a -> eq (compose (const c) f a) (const c a)

::::::::::::::::::::
::::::::::::::::::::

$\flip$ lets us, well, flip the arguments of a function.

:::::: definition ::
[]{#def-flip}
Let $A$, $B$, and $C$ be sets. Given $f : A \rightarrow C^B$, we define $\flip(f) : B \rightarrow C^A$ by $$\flip(f)(b)(a) = f(a)(b).$$

In Haskell:

> flip :: (a -> b -> c) -> b -> a -> c
> flip f b a = f a b

::::::::::::::::::::

$\flip$ is an involution.

:::::: theorem :::::
[]{#thm-flip-involution}
Let $A$, $B$, and $C$ be sets. For all $f : A \rightarrow C^B$, we have $$\flip(\flip(f)) = f.$$

::: proof ::::::::::
Let $a \in A$ and $b \in B$. Then we have
$$\begin{eqnarray*}
 &   & \flip(\flip(f))(a)(b) \\
 &     \href{@functions@#def-flip}
   = & \flip(f)(b)(a) \\
 &     \href{@functions@#def-flip}
   = & f(a)(b)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip_involution :: (Equal c)
>   => a -> b -> c -> Test ((a -> b -> c) -> a -> b -> Bool)
> _test_flip_involution _ _ _ =
>   testName "flip(flip(f)) == f" $
>   \f a b -> eq (flip (flip f) a b) (f a b)

::::::::::::::::::::
::::::::::::::::::::

$\apply$ is operatorized function application.

:::::: definition ::
[]{#def-apply}
Given $f : A \rightarrow B$ and $x \in A$, we define $$\apply(f)(x) = f(x).$$

In Haskell:

> apply :: (a -> b) -> a -> b
> apply f x = f x

::::::::::::::::::::

$\apply$ distributes over compose.

:::::: theorem :::::
[]{#thm-apply-compose-distribute}
If $f : A \rightarrow B$ and $g : B \rightarrow C$ we have $$\apply(\compose(g)(f)) = \compose(\apply(g))(\apply(f)).$$

::: proof ::::::::::
Let $x \in A$. Now we have
$$\begin{eqnarray*}
 &   & \apply(\compose(g)(f))(x) \\
 &     \href{@functions@#def-apply}
   = & \compose(g)(f)(x) \\
 &     \href{@functions@#def-compose}
   = & g(f(x)) \\
 &     \href{@functions@#def-apply}
   = & \apply(g)(f(x)) \\
 &     \href{@functions@#def-apply}
   = & \apply(g)(\apply(f)(x)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\apply(g))(\apply(f))(x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_apply_compose_distribute :: (Equal c)
>   => a -> b -> c -> Test ((b -> c) -> (a -> b) -> a -> Bool)
> _test_apply_compose_distribute _ _ _ =
>   testName "apply(compose(g)(f)) == compose(apply(g))(apply(f))" $
>   \g f x -> eq (apply (compose g f) x) (compose (apply g) (apply f) x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_functions ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b
>   , Equal c, Show c, Arbitrary c, CoArbitrary c
>   , Equal d, Show d, Arbitrary d, CoArbitrary d
>   ) => a -> b -> c -> d -> Int -> Int -> IO ()
> _test_functions a b c d size num = do
>   testLabel0 "Functions"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_compose_id_left a b)
>   runTest args (_test_compose_id_right a b)
>   runTest args (_test_compose_associative a b c d)
>   runTest args (_test_compose_const_left a b c)
>   runTest args (_test_flip_involution a b c)
>   runTest args (_test_apply_compose_distribute a b c)

Main:

> main_functions :: IO ()
> main_functions = do
>   _test_functions () () () () 1 1
