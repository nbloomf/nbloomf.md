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
[]{#def-and}
We define a map $\band : \bool \times \bool \rightarrow \bool$ by $$\band(p,q) = \bif{p}{\bif{q}{\btrue}{\bfalse}}{\bfalse}.$$

In Haskell: 

> and :: (Boolean b) => b -> b -> b
> and p q = ifThenElse p (ifThenElse q true false) false

::::::::::::::::::::

We can compute $\band$ explicitly.

:::::: theorem :::::
[]{#thm-and-eval}[]{#thm-and-eval-true-true}[]{#thm-and-eval-true-false}[]{#thm-and-eval-false-true}[]{#thm-and-eval-false-false}
We have
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
 &     \href{@and@#def-and}
   = & \bif{\btrue}{\bif{\btrue}{\btrue}{\bfalse}}{\bfalse} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\btrue}{\bfalse} \\
 &     \href{@booleans@#cor-if-true}
   = & \btrue
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \band(\btrue,\bfalse) \\
 &     \href{@and@#def-and}
   = & \bif{\btrue}{\bif{\bfalse}{\btrue}{\bfalse}}{\bfalse} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\btrue}{\bfalse}{\bfalse} \\
 &     \href{@booleans@#cor-if-true}
   = & \bfalse
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \band(\bfalse,\btrue) \\
 &     \href{@and@#def-and}
   = & \bif{\bfalse}{\bif{\btrue}{\btrue}{\bfalse}}{\bfalse} \\
 &     \href{@booleans@#cor-if-false}
   = & \bfalse
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bfalse) \\
 &     \href{@and@#def-and}
   = & \bif{\bfalse}{\bif{\bfalse}{\btrue}{\bfalse}}{\bfalse} \\
 &     \href{@booleans@#cor-if-false}
   = & \bfalse
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
[]{#thm-and-false}[]{#thm-and-false-left}[]{#thm-and-false-right}
If $a \in \bool$, we have $$\band(\bfalse,a) = \band(a,\bfalse) = \bfalse.$$

::: proof ::::::::::
If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\btrue) \\
 &     \href{@and@#thm-and-eval-false-true}
   = & \bfalse \\
 &     \href{@and@#thm-and-eval-true-false}
   = & \band(\btrue,\bfalse)
\end{eqnarray*}$$
and if $a = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bfalse) \\
 &     \href{@and@#thm-and-eval-false-false}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
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
[]{#thm-and-true}[]{#thm-and-true-left}[]{#thm-and-true-right}
If $a \in \bool$, we have $$\band(\btrue,a) = \band(a,\btrue) = a.$$

::: proof ::::::::::
If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
and if $a = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\bfalse) \\
 &     \href{@and@#thm-and-eval-true-false}
   = & \bfalse \\
 &     \href{@and@#thm-and-eval-false-true}
   = & \band(\bfalse,\btrue)
\end{eqnarray*}$$
as claimed.
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
[]{#thm-and-not}
If $a \in \bool$, we have $\band(a,\bnot(a)) = \bfalse$.

::: proof ::::::::::
If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\bnot(\btrue)) \\
 &     \href{@not@#thm-not-true}
   = & \band(\btrue,\bfalse) \\
 &     \href{@and@#thm-and-eval-true-false}
   = & \bfalse
\end{eqnarray*}$$
and if $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bnot(\bfalse)) \\
 &     \href{@and@#thm-and-false-left}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
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
[]{#thm-and-idempotent}
If $a \in \bool$, we have $\band(a,a) = a$.

::: proof ::::::::::
If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
and if $a = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bfalse) \\
 &     \href{@and@#thm-and-eval-false-false}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
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
[]{#thm-and-commutative}
If $a,b \in \bool$, we have $\band(a,b) = \band(b,a)$.

::: proof ::::::::::
If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \band(\btrue,b) \\
 &     \href{@and@#thm-and-true-left}
   = & b \\
 &     \href{@and@#thm-and-true-right}
   = & \band(b,\btrue)
\end{eqnarray*}$$
and if $a = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,b)
 &     \href{@and@#thm-and-false-left}
   = & \bfalse \\
 &     \href{@and@#thm-and-false-right}
   = & \band(b,\bfalse)
\end{eqnarray*}$$
as claimed.
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
[]{@#thm-and-associative}
For all $a,b,c \in \bool$, we have $$\band(\band(a,b),c) = \band(a,\band(b,c)).$$

::: proof ::::::::::
If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\btrue,b),c) \\
 &     \href{@and@#thm-and-true-left}
   = & \band(b,c) \\
 &     \href{@and@#thm-and-true-left}
   = & \band(\btrue,\band(b,c)) \\
 & = & \band(a,\band(b,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\bfalse,b),c) \\
 &     \href{@and@#thm-and-false-left}
   = & \band(\bfalse,c) \\
 &     \href{@and@#thm-and-false-left}
   = & \bfalse \\
 &     \href{@and@#thm-and-false-left}
   = & \band(\bfalse,\band(b,c))
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
[]{#thm-and-if-right}
Let $p,q,r \in \bool$. Then we have $$\band(p,\bif{p}{q}{r}) = \band(p,q).$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\btrue,\bif{\btrue}{q}{r}) \\
 &     \href{@booleans@#cor-if-true}
   = & \band(\btrue,q) \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\bfalse,\bif{\bfalse}{q}{r}) \\
 &     \href{@and@#thm-and-false-left}
   = & \bfalse \\
 &     \href{@and@#thm-and-false-left}
   = & \band(\bfalse,q)
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
[]{#thm-and-if-hyp}
Let $A$ be a set with $a,b \in A$, and let $p,q \in \bool$. Then we have $$\bif{\band(p,q)}{a}{b} = \bif{p}{\bif{q}{a}{b}}{b}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\btrue,q)}{a}{b} \\
 &     \href{@and@#thm-and-true-left}
   = & \bif{q}{a}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\bif{q}{a}{b}}{b}
\end{eqnarray*}$$
and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\bfalse,q)}{a}{b} \\
 &     \href{@and@#thm-and-false-left}
   = & \bif{\bfalse}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bif{q}{a}{b}}{b}
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
