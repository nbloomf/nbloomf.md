---
title: Implies
author: nbloomf
date: 2018-01-18
tags: arithmetic-made-difficult, literate-haskell
slug: implies
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Implies (
>   impl, _test_impl, main_impl
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or

Next we define implication on booleans.

:::::: definition ::
We define $\bimpl : \bool \times \bool \rightarrow \bool$ by $$\bimpl(p,q) = \bif{p}{q}{\btrue}.$$

In Haskell:

> impl :: (Boolean b) => b -> b -> b
> impl p q = ifThenElse p q true

::::::::::::::::::::

$\bimpl$ is equivalent to an $\bor$.

:::::: theorem :::::
For all $p,q \in \bool$, we have $$\bimpl(p,q) = \bor(\bnot(p),q).$$

::: proof ::::::::::
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,q) \\
 & = & \bif{\bfalse}{q}{\btrue} \\
 &     \href{@booleans@#cor-if-false}
   = & \btrue \\
 & = & \bor(\btrue,q) \\
 &     \href{@not@#thm-not-false}
   = & \bor(\bnot(\bfalse),q)
\end{eqnarray*}$$
as needed. Suppose then that $p = \btrue$. Then
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,q) \\
 & = & \bif{\btrue}{q}{\btrue} \\
 &     \href{@booleans@#cor-if-true}
   = & q \\
 & = & \bor(\bfalse,q) \\
 &     \href{@not@#thm-not-true}
   = & \bor(\bnot(\btrue),q)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_or :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_impl_or _ =
>   testName "impl(p,q) == or(not(p),q)" $
>   \p q -> eq (impl p q) (or (not p) q) 

::::::::::::::::::::
::::::::::::::::::::

$\bfalse$ implies anything.

:::::: theorem :::::
If $p \in \bool$, we have $\bimpl(\bfalse,p) = \btrue$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,p) \\
 & = & \bor(\bnot(\bfalse),p) \\
 &     \href{@not@#thm-not-false}
   = & \bor(\btrue,p) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_false :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_false _ =
>   testName "impl(false,p) == true" $
>   \p -> eq (impl false p) true

::::::::::::::::::::
::::::::::::::::::::

$\btrue$ is left-neutral.

:::::: theorem :::::
For all $p \in \bool$ we have $\bimpl(\btrue,p) = p$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,p) \\
 & = & \bor(\bnot(\btrue),p) \\
 &     \href{@not@#thm-not-true}
   = & \bor(\bfalse,p) \\
 & = & p
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_true :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_true _ =
>   testName "impl(true,p) == p" $
>   \p -> eq (impl true p) p

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ is... idemp-constant? Not sure what to call this.

:::::: theorem :::::
If $p \in \bool$ we have $\bimpl(p,p)$.

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,\btrue) \\
 & = & \bor(\bnot(\btrue),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_reflexive :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_reflexive _ =
>   testName "impl(p,p) == true" $
>   \p -> eq (impl p p) true

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ is antisymmetric.

:::::: theorem :::::
For all $p,q \in \bool$ we have $\bor(\bimpl(p,q),\bimpl(q,p))$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bor(\bimpl(p,q),\bimpl(q,p)) \\
 & = & \bor(\bor(\bnot(p),q),\bor(\bnot(q),p)) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bnot(p),\bor(q,\bor(\bnot(q),p))) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bnot(p),\bor(\bor(q,\bnot(q)),p)) \\
 &     \href{@or@#thm-or-not}
   = & \bor(\bnot(p),\bor(\btrue,p)) \\
 &     \href{@or@#thm-or-true-left}
   = & \bor(\bnot(p),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_total :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_impl_total _ =
>   testName "or(impl(p,q),impl(q,p)) == true" $
>   \p q -> eq (or (impl p q) (impl q p)) true

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ is left-commutative.

:::::: theorem :::::
For all $p,q,r \in \bool$ we have $$\bimpl(p,\bimpl(q,r)) = \bimpl(q,\bimpl(p,r)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bor(\bnot(q),r)) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bor(\bnot(p),\bnot(q)),r) \\
 &     \href{@or@#thm-or-commutative}
   = & \bor(\bor(\bnot(q),\bnot(p)),r) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bnot(q),\bor(\bnot(p),r)) \\
 & = & \bor(\bnot(q),\bimpl(p,r)) \\
 &   & \bimpl(q,\bimpl(p,r))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_antecedents_commute :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_impl_antecedents_commute _ =
>   testName "impl(p,impl(q,r)) == impl(q,impl(p,r))" $
>   \p q r -> eq (impl p (impl q r)) (impl q (impl p r))

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ has a kind of transitivity.

:::::: theorem :::::
For all $p,q,r \in \bool$ we have $$\bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bimpl(q,r)),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\bnot(\bor(\bnot(p),q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 &     \href{@or@#thm-demorgan-not-or}
   = & \bor(\band(\bnot(\bnot(p)),\bnot(q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 &     \href{@or@#thm-demorgan-not-or}
   = & \bor(\band(p,\bnot(q)),\bor(\band(\bnot(\bnot(q)),\bnot(r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(p),r))) \\
 & = & Q.
\end{eqnarray*}$$
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\bfalse),r))) \\
 &     \href{@not@#thm-not-false}
   = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\btrue,r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\btrue)) \\
 &     \href{@or@#thm-or-true-right}
   = & \bor(\band(p,\bnot(q)),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(\btrue,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\btrue),r))) \\
 & = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),\bor(\bfalse,r))) \\
 &     \href{@or@#thm-or-false-left}
   = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),r)) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\bor(\bnot(r),r))) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\btrue)) \\
 &     \href{@and@#thm-and-true-right}
   = & \bor(\bnot(q),\bor(q,r)) \\
 & = & \bor(\bor(\bnot(q),q),r) \\
 & = & \bor(\btrue,r) \\
 &     \href{@or@#thm-or-true-left}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_transitive :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_impl_transitive _ =
>   testName "impl(impl(p,q),impl(impl(q,r),impl(p,r)))" $
>   \p q r -> isTrue $ impl (impl p q) (impl (impl q r) (impl p r))

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ has a kind of distributivity.

:::::: theorem :::::
For all $p,q,r \in \bool$ we have $$\bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))).$$

::: proof ::::::::::
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 & = & \bimpl(\bimpl(\bfalse,\bimpl(q,r)),\bimpl(\bimpl(\bfalse,q),\bimpl(\bfalse,r))) \\
 & = & \bimpl(\btrue,\bimpl(\btrue,\btrue)) \\
 & = & \bimpl(\btrue,\btrue) \\
 & = & \btrue.
\end{eqnarray*}$$
Suppose instead that $p = \btrue$. Now
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 & = & \bimpl(\bimpl(\btrue,\bimpl(q,r)),\bimpl(\bimpl(\btrue,q),\bimpl(\btrue,r))) \\
 & = & \bimpl(\bimpl(q,r),\bimpl(q,r)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_distributive :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_impl_distributive _ =
>   testName "impl(impl(p,impl(q,r)),impl(impl(p,q),impl(p,r)))" $
>   \p q r -> isTrue $ impl (impl p (impl q r)) (impl (impl p q) (impl p r))

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ interacts with $\band$.

:::::: theorem :::::
For all $p,q,r,s \in \bool$, if $\bimpl(p,r)$ and $\bimpl(q,s)$, then $\bimpl(\band(p,q),\band(r,s))$.

::: proof ::::::::::
If $p = \bfalse$, then
$$\begin{eqnarray*}
 &   & \bimpl(\band(p,q),\band(r,s)) \\
 & = & \bimpl(\band(\bfalse,q),\band(r,s)) \\
 &     \href{@and@#thm-and-false-left}
   = & \bimpl(\bfalse,\band(r,s))
 & = & \btrue.
\end{eqnarray*}$$
Similarly if $q = \bfalse$. Suppose then that $p = q = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \bimpl(p,r) \\
 & = & \bimpl(\btrue,r) \\
 & = & r,
\end{eqnarray*}$$
and similarly $s = \btrue$. Then
$$\begin{eqnarray*}
 &   & \bimpl(\band(p,q),\band(r,s)) \\
 & = & \bimpl(\band(\btrue,\btrue),\band(\btrue,\btrue)) \\
 & = & \bimpl(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_and_compatible :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> b -> Bool)
> _test_impl_and_compatible b =
>   testName "if and(impl(p,r),impl(q,s)) then impl(and(p,q),and(r,s))" $
>   \p q r s -> isTrue $ ifThenElse (and (impl p r) (impl q s))
>     (impl (and p q) (and r s))
>     (true)

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ interacts with $\band$ and $\bif{\ast}{\ast}{\ast}$.

$\band$ interacts with $\bif{\ast}{\ast}{\ast}$.

:::::: theorem :::::
Let $p,q,r \in \bool$. If $\bimpl(r,q)$, then $$\bif{\band(p,q)}{\btrue}{r} = \bif{p}{q}{r}.$$

::: proof ::::::::::
If $r = \btrue$, then $q = \btrue$. Now
$$\begin{eqnarray*}
 &   & \bif{\band(p,\btrue)}{\btrue}{\btrue} \\
 &     \href{@and@#thm-and-true-right}
   = & \bif{p}{\btrue}{\btrue}
\end{eqnarray*}$$
as needed. Suppose instead that $r = \bfalse$. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\btrue,q)}{\btrue}{\bfalse} \\
 &     \href{@and@#thm-and-true-left}
   = & \bif{q}{\btrue}{\bfalse} \\
 & = & q \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{q}{\bfalse}
\end{eqnarray*}$$
as needed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{\band(\bfalse,q)}{\btrue}{r} \\
 &     \href{@and@#thm-and-false-left}
   = & \bif{\bfalse}{\btrue}{r} \\
 &     \href{@booleans@#cor-if-false}
   = & r \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{q}{r}
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_and_if :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_impl_and_if _ =
>   testName "if impl(r,q) then if(and(p,q),true,r) == if(p,q,r)" $
>   \p q r -> if isTrue (impl r q)
>     then eq
>       (ifThenElse (and p q) true r)
>       (ifThenElse p q r)
>     else true

::::::::::::::::::::
::::::::::::::::::::



Testing
-------

Suite:

> _test_impl ::
>   ( TypeName b, Boolean b, Arbitrary b, Show b, Equal b
>   ) => b -> Int -> Int -> IO ()
> _test_impl p size num = do
>   testLabel1 "implies" p
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_impl_or p)
>   runTest args (_test_impl_false p)
>   runTest args (_test_impl_true p)
>   runTest args (_test_impl_reflexive p)
>   runTest args (_test_impl_total p)
>   runTest args (_test_impl_antecedents_commute p)
>   runTest args (_test_impl_transitive p)
>   runTest args (_test_impl_distributive p)
>   runTest args (_test_impl_and_compatible p)
>   runTest args (_test_impl_and_if p)

Main:

> main_impl :: IO ()
> main_impl = _test_impl (true :: Bool) 20 100
