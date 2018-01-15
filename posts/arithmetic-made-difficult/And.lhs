---
title: And
author: nbloomf
date: 2018-01-15
tags: arithmetic-made-difficult, literate-haskell
slug: and
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module And (
>   and, _test_and, main_and
> ) where
> 
> import Testing
> import Booleans
> import Not

Next, $\band$.

:::::: definition ::
[](#def-and) We define a map $\band : \bool \times \bool \rightarrow \bool$ by $$\band(p,q) = \bif{p}{\bif{q}{\btrue}{\bfalse}}{\bfalse}.$$

In Haskell: 

> and :: (Boolean b) => b -> b -> b
> and p q = ifThenElse p (ifThenElse q true false) false

::::::::::::::::::::

We can compute $\band$ explicitly.

:::::: theorem :::::
[](#and-eval) We have
$$\begin{eqnarray*}
\band(\btrue,\btrue)   & = & \btrue \\
\band(\btrue,\bfalse)  & = & \bfalse \\
\band(\bfalse,\btrue)  & = & \bfalse \\
\band(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$

::: proof ::::::::::
(@@@)
::::::::::::::::::::

::: test :::::::::::

> _test_and_true_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_and_true_true p =
>   testName "and(true,true) == true" $
>   eq (and true true) (true `withTypeOf` p)

::::::::::::::::::::
::::::::::::::::::::

And $\band$ satisfies the usual properties.

:::::: theorem :::::
The following hold for all $a,b,c \in \bool$.

1. $\band(\bfalse,a) = \band(a,\bfalse) = \bfalse$.
2. $\band(\btrue,a) = \band(a,\btrue) = a$.
3. $\band(a,\bnot(a)) = \bfalse$.
4. $\band(a,a) = a$.
5. $\band(a,b) = \band(b,a)$.
6. $\band(\band(a,b),c) = \band(a,\band(b,c))$.

::: proof ::::::::::
1. If $a = \btrue$ we have $$\band(\bfalse,\btrue) = \bfalse = \band(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
2. If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\btrue,\bfalse) = \bfalse = \band(\bfalse,\btrue)$$ as claimed.
3. If $a = \btrue$, we have $\band(\btrue,\bnot(\btrue)) = \band(\btrue,\bfalse) = \bfalse,$$ and if $a = \bfalse$, we have $$\band(\bfalse,\bnot(\bfalse)) = \bfalse$$ as claimed.
4. If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
5. If $a = \btrue$ we have $$\band(\btrue,b) = b = \band(b,\btrue),$$ and if $a = \bfalse$ we have $$\band(\bfalse,b) = \bfalse = \band(b,\bfalse)$$ as claimed.
6. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\btrue,b),c) \\
 & = & \band(b,c) \\
 & = & \band(\btrue,\band(b,c)) \\
 & = & \band(a,\band(b,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\bfalse,b),c) \\
 & = & \band(\bfalse,c) \\
 & = & \bfalse \\
 & = & \band(\bfalse,\band(b,c))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_false :: Test (Bool -> Bool)
> _test_and_false =
>   testName "and(false,p) == false" $
>   \p -> eq (and false p) false
> 
> 
> _test_and_true :: Test (Bool -> Bool)
> _test_and_true =
>   testName "and(true,p) == p" $
>   \p -> eq (and true p) p
> 
> 
> _test_and_not :: Test (Bool -> Bool)
> _test_and_not =
>   testName "and(p,not(p)) == false" $
>   \p -> eq (and p (not p)) false
> 
> 
> _test_and_idempotent :: Test (Bool -> Bool)
> _test_and_idempotent =
>   testName "and(p,p) == p" $
>   \p -> eq (and p p) p
> 
> 
> _test_and_commutative :: Test (Bool -> Bool -> Bool)
> _test_and_commutative =
>   testName "and(p,q) == and(q,p)" $
>   \p q -> eq (and p q) (and q p)
> 
> 
> _test_and_associative :: Test (Bool -> Bool -> Bool -> Bool)
> _test_and_associative =
>   testName "and(and(p,q),r) == and(p,and(q,r))" $
>   \p q r -> eq (and (and p q) r) (and p (and q r))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_and ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a
>   , Boolean b, Arbitrary b, Show b, Equal b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_and p x size num = do
>   testLabel0 "Bool"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_and_true_true p)
> 
>   runTest args _test_and_false
>   runTest args _test_and_true
>   runTest args _test_and_not
>   runTest args _test_and_idempotent
>   runTest args _test_and_commutative
>   runTest args _test_and_associative

Main:

> main_and :: IO ()
> main_and = _test_and (true :: Bool) (true :: Bool) 20 100
