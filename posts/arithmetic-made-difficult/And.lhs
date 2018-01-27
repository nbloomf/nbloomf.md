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
[](#thm-and-eval) We have
$$\begin{eqnarray*}
\band(\btrue,\btrue)   & = & \btrue \\
\band(\btrue,\bfalse)  & = & \bfalse \\
\band(\bfalse,\btrue)  & = & \bfalse \\
\band(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \band(\btrue,\btrue) \\
 & = & \bif{\btrue}{\bif{\btrue}{\btrue}{\bfalse}}{\bfalse} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\btrue}{\bfalse} \\
 & = & \btrue,
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \band(\btrue,\bfalse) \\
 & = & \bif{\btrue}{\bif{\bfalse}{\btrue}{\bfalse}}{\bfalse} \\
 & = & \bif{\btrue}{\bfalse}{\bfalse} \\
 & = & \bfalse,
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \band(\bfalse,\btrue) \\
 & = & \bif{\bfalse}{\bif{\btrue}{\btrue}{\bfalse}}{\bfalse} \\
 & = & \bfalse,
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bfalse) \\
 & = & \bif{\bfalse}{\bif{\bfalse}{\btrue}{\bfalse}}{\bfalse} \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_true_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_and_true_true p =
>   testName "and(true,true) == true" $
>   eq (and true true) (true `withTypeOf` p)
> 
> 
> _test_and_true_false :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_and_true_false p =
>   testName "and(true,false) == false" $
>   eq (and true false) (false `withTypeOf` p)
> 
> 
> _test_and_false_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_and_false_true p =
>   testName "and(false,true) == false" $
>   eq (and false true) (false `withTypeOf` p)
> 
> 
> _test_and_false_false :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_and_false_false p =
>   testName "and(false,false) == false" $
>   eq (and false false) (false `withTypeOf` p)

::::::::::::::::::::
::::::::::::::::::::

$\bfalse$ absorbs under $\band$.

:::::: theorem :::::
If $a \in \bool$, we have $$\band(\bfalse,a) = \band(a,\bfalse) = \bfalse.$$

::: proof ::::::::::
If $a = \btrue$ we have $$\band(\bfalse,\btrue) = \bfalse = \band(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_false :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_and_false b =
>   testName "and(false,p) == false" $
>   \p -> eq (and false p) (false `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

$\btrue$ is neutral under $\band$.

:::::: theorem :::::
If $a \in \bool$, we have $$\band(\btrue,a) = \band(a,\btrue) = a.$$

::: proof ::::::::::
If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\btrue,\bfalse) = \bfalse = \band(\bfalse,\btrue)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_true :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_and_true _ =
>   testName "and(true,p) == p" $
>   \p -> eq (and true p) p

::::::::::::::::::::
::::::::::::::::::::

$\band$ interacts with $\bnot$.

:::::: theorem :::::
If $a \in \bool$, we have $\band(a,\bnot(a)) = \bfalse$.

::: proof ::::::::::
If $a = \btrue$, we have $\band(\btrue,\bnot(\btrue)) = \band(\btrue,\bfalse) = \bfalse,$$ and if $a = \bfalse$, we have $$\band(\bfalse,\bnot(\bfalse)) = \bfalse$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_not :: (Boolean b, Equal b)
>  => b -> Test (b -> Bool)
> _test_and_not b =
>   testName "and(p,not(p)) == false" $
>   \p -> eq (and p (not p)) (false `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

$\band$ is idempotent.

:::::: theorem :::::
If $a \in \bool$, we have $\band(a,a) = a$.

::: proof ::::::::::
If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_idempotent :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_and_idempotent _ =
>   testName "and(p,p) == p" $
>   \p -> eq (and p p) p

::::::::::::::::::::
::::::::::::::::::::

$\band$ is commutative.

:::::: theorem :::::
If $a,b \in \bool$, we have $\band(a,b) = \band(b,a)$.

::: proof ::::::::::
If $a = \btrue$ we have $$\band(\btrue,b) = b = \band(b,\btrue),$$ and if $a = \bfalse$ we have $$\band(\bfalse,b) = \bfalse = \band(b,\bfalse)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_commutative :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_and_commutative _ =
>   testName "and(p,q) == and(q,p)" $
>   \p q -> eq (and p q) (and q p)

::::::::::::::::::::
::::::::::::::::::::

$\band$ is associative.

:::::: theorem :::::
For all $a,b,c \in \bool$, we have $$\band(\band(a,b),c) = \band(a,\band(b,c)).$$

::: proof ::::::::::
If $a = \btrue$, we have
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

> _test_and_associative :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_and_associative _ =
>   testName "and(and(p,q),r) == and(p,and(q,r))" $
>   \p q r -> eq (and (and p q) r) (and p (and q r))

::::::::::::::::::::
::::::::::::::::::::

$\band$ interacts with $\bif{\ast}{\ast}{\ast}$ in the second argument.

:::::: theorem :::::
Let $p,q,r \in \bool$. Then we have $$\band(p,\bif{p}{q}{r}) = \band(p,q).$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\bif{\btrue}{q}{r}) \\
 & = & \band(\btrue,q) \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bif{\bfalse}{q}{r}) \\
 & = & \bfalse \\
 & = & \band(\bfalse,q)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_if_cancel :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_and_if_cancel _ =
>   testName "and(p,if(p,q,r)) == and(p,q)" $
>   \p q r -> eq (and p (ifThenElse p q r)) (and p q)

::::::::::::::::::::
::::::::::::::::::::

$\band$ in the hypothesis of $\bif{\ast}{\ast}{\ast}$ expands.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$, and let $p,q \in \bool$. Then we have $$\bif{\band(p,q)}{a}{b} = \bif{p}{\bif{q}{a}{b}}{b}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\btrue,q)}{a}{b} \\
 & = & \bif{q}{a}{b} \\
 & = & \bif{\btrue}{\bif{q}{a}{b}}{b},
\end{eqnarray*}$$
and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\bfalse,q)}{a}{b} \\
 & = & \bif{\bfalse}{a}{b} \\
 & = & b \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{b}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_and_if_hypothesis :: (Boolean b, Equal b, Equal a)
>   => b -> a -> Test (b -> b -> a -> a -> Bool)
> _test_and_if_hypothesis _ _ =
>   testName "if(and(p,q),a,b) == if(p,if(q,a,b),b)" $
>   \p q a b -> eq
>     (ifThenElse (and p q) a b)
>     (ifThenElse p (ifThenElse q a b) b)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_and ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a, TypeName a
>   , Boolean b, Arbitrary b, Show b, Equal b, TypeName b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_and p x size num = do
>   testLabel2 "and" p x
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_and_true_true p)
>   runTest args (_test_and_true_false p)
>   runTest args (_test_and_false_true p)
>   runTest args (_test_and_false_false p)
>   runTest args (_test_and_false p)
>   runTest args (_test_and_true p)
>   runTest args (_test_and_not p)
>   runTest args (_test_and_idempotent p)
>   runTest args (_test_and_commutative p)
>   runTest args (_test_and_associative p)
>   runTest args (_test_and_if_cancel p)
>   runTest args (_test_and_if_hypothesis p x)

Main:

> main_and :: IO ()
> main_and = _test_and (true :: Bool) (true :: Bool) 20 100
