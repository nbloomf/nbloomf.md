---
title: Not
author: nbloomf
date: 2018-01-14
tags: arithmetic-made-difficult, literate-haskell
slug: not
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Not (
>   not, _test_not, main_not
> ) where
> 
> import Testing
> import Booleans

In the last post, we defined the booleans $\bool$. We can define the usual logical operators in terms of $\bif{\ast}{\ast}{\ast}$. First, $\bnot$.

:::::: definition ::
[]{#def-not}
We define $\bnot : \bool \rightarrow \bool$ by $$\bnot(p) = \bif{p}{\bfalse}{\btrue}.$$

In Haskell:

> not :: (Boolean b) => b -> b
> not p = ifThenElse p false true

::::::::::::::::::::

We can compute $\bnot$ explicitly.

:::::: theorem :::::
[]{#thm-not-true}[#thm-not-false]{}
We have $\bnot(\btrue) = \bfalse$ and $\bnot(\bfalse) = \btrue$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \bnot(\btrue) \\
 &     \href{@not@#def-not}
   = & \bif{\btrue}{\bfalse}{\btrue} \\
 &     \href{@booleans@#cor-if-true}
   = & \bfalse
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \bnot(\bfalse) \\
 &     \href{@not@#def-not}
   = & \bif{\bfalse}{\bfalse}{\btrue} \\
 &     \href{@booleans@#cor-if-false}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_not_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_not_true p =
>   testName "not(true) == false" $
>   eq (not (true `withTypeOf` p)) false
> 
> 
> _test_not_false :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_not_false p =
>   testName "not(false) == true" $
>   eq (not (false `withTypeOf` p)) true

::::::::::::::::::::
::::::::::::::::::::

$\bnot$ is an involution.

:::::: theorem :::::
[]{#thm-not-involution}
For all $a \in \bool$ we have $\bnot(\bnot(a)) = a$.

::: proof ::::::::::
If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \bnot(\bnot(\btrue)) \\
 &     \href{@not@#thm-not-true}
   = & \bnot(\bfalse) \\
 &     \href{@not@#thm-not-false}
   = & \btrue
\end{eqnarray*}$$
and if $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bnot(\bnot(\bfalse)) \\
 &     \href{@not@#thm-not-false}
   = & \bnot(\btrue) \\
 &     \href{@not@#thm-not-true}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_not_involutive :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_not_involutive _ =
>   testName "not(not(p)) == p" $
>   \p -> eq (not (not p)) p

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ interacts with $\bnot$.

:::::: theorem :::::
[]{#thm-ifnot}
Let $A$ be a set with $p \in \bool$ and $a,b \in A$. We have $$\bif{\bnot(p)}{a}{b} = \bif{p}{b}{a}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\bnot(p)}{a}{b} \\
 &     \let{p = \btrue}
   = & \bif{\bnot(\btrue)}{a}{b} \\
 &     \href{@not@#thm-not-true}
   = & \bif{\bfalse}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{b}{a} \\
 &     \let{p = \btrue}
   = & \bif{p}{b}{a}
\end{eqnarray*}$$
and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{\bnot(p)}{a}{b} \\
 &     \let{p = \bfalse}
   = & \bif{\bnot(\bfalse)}{a}{b} \\
 &     \href{@not@#thm-not-false}
   = & \bif{\btrue}{a}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{b}{a} \\
 &     \let{p = \bfalse}
   = & \bif{p}{b}{a}
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_not :: (Equal a) => a -> Test (Bool -> a -> a -> Bool)
> _test_if_not _ =
>   testName "if(not(p),a,b) == if(p,b,a)" $
>   \p a b -> eq (ifThenElse (not p) a b) (ifThenElse p b a)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_not ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a
>   , Boolean b, Arbitrary b, Show b, Equal b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_not p x size num = do
>   testLabel0 "Bool"
> 
>   let
~ args = testArgs size cases
>  
>   runTest args (_test_not_true p)
>   runTest args (_test_not_false p)
>   runTest args (_test_not_involutive p)
>   runTest args (_test_if_not x)

Main:

> main_not :: IO ()
> main_not = _test_not (true :: Bool) (true :: Bool) 20 100
