---
title: Implies
author: nbloomf
date: 2018-01-14
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



Implication on booleans:

:::::: definition ::
We define $\bimpl : \bool \times \bool \rightarrow \bool$ by $$\bimpl(p,q) = \bor(\bnot(p),q).$$

In Haskell:

> impl :: Bool -> Bool -> Bool
> impl p q = ifThenElse p (ifThenElse q true false) true

::::::::::::::::::::

And implication has its own properties.

:::::: theorem :::::
For all $p,q,r,s \in \bool$ we have the following.

1. $\bimpl(\bfalse,p) = \btrue$.
2. $\bimpl(\btrue,p) = p$.
3. $\bimpl(p,p)$.
4. $\bor(\bimpl(p,q),\bimpl(q,p))$.
5. $\bimpl(p,\bimpl(q,r)) = \bimpl(q,\bimpl(p,r))$.
6. $\bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r)))$.
7. $\bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r)))$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,p) \\
 & = & \bor(\bnot(\bfalse),p) \\
 & = & \bor(\btrue,p) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,p) \\
 & = & \bor(\bnot(\btrue),p) \\
 & = & \bor(\bfalse,p) \\
 & = & p
\end{eqnarray*}$$
as claimed.
3. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,\btrue) \\
 & = & \bor(\bnot(\btrue),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \bor(\bimpl(p,q),\bimpl(q,p)) \\
 & = & \bor(\bor(\bnot(p),q),\bor(\bnot(q),p)) \\
 & = & \bor(\bnot(p),\bor(q,\bor(\bnot(q),p))) \\
 & = & \bor(\bnot(p),\bor(\bor(q,\bnot(q)),p)) \\
 & = & \bor(\bnot(p),\bor(\btrue,p)) \\
 & = & \bor(\bnot(p),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
5. We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bor(\bnot(q),r)) \\
 & = & \bor(\bor(\bnot(p),\bnot(q)),r) \\
 & = & \bor(\bor(\bnot(q),\bnot(p)),r) \\
 & = & \bor(\bnot(q),\bor(\bnot(p),r)) \\
 & = & \bor(\bnot(q),\bimpl(p,r)) \\
 &   & \bimpl(q,\bimpl(p,r))
\end{eqnarray*}$$
as claimed.
6. We have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bimpl(q,r)),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\bnot(\bor(\bnot(p),q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(\bnot(\bnot(p)),\bnot(q))),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(\bnot(\bnot(q)),\bnot(r))),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(p),r))) \\
 & = & Q.
\end{eqnarray*}$$
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\bfalse),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\btrue,r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\btrue)) \\
 & = & \bor(\band(p,\bnot(q)),\btrue) \\
 & = & \btrue.
\end{eqnarray*}$$
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(\btrue,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\btrue),r))) \\
 & = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),\bor(\bfalse,r))) \\
 & = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),r)) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\bor(\bnot(r),r))) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\btrue)) \\
 & = & \bor(\bnot(q),\bor(q,r)) \\
 & = & \bor(\bor(\bnot(q),q),r) \\
 & = & \bor(\btrue,r) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
7. If $p = \bfalse$, we have
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
 & = & \bimpl(\bimpl(q,r),\bimpl(\bimpl(q,r)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_false :: Test (Bool -> Bool)
> _test_impl_false =
>   testName "impl(false,p) == true" $
>   \p -> eq (impl false p) true
> 
> 
> _test_impl_true :: Test (Bool -> Bool)
> _test_impl_true =
>   testName "impl(true,p) == p" $
>   \p -> eq (impl true p) p
> 
> 
> _test_impl_reflexive :: Test (Bool -> Bool)
> _test_impl_reflexive =
>   testName "impl(p,p) == true" $
>   \p -> eq (impl p p) true
> 
> 
> _test_impl_total :: Test (Bool -> Bool -> Bool)
> _test_impl_total =
>   testName "or(impl(p,q),impl(q,p)) == true" $
>   \p q -> eq (or (impl p q) (impl q p)) true
> 
> 
> _test_impl_antecedents_commute :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_antecedents_commute =
>   testName "impl(p,impl(q,r)) == impl(q,impl(p,r))" $
>   \p q r -> eq (impl p (impl q r)) (impl q (impl p r))
> 
> 
> _test_impl_transitive :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_transitive =
>   testName "impl(impl(p,q),impl(impl(q,r),impl(p,r)))" $
>   \p q r -> impl (impl p q) (impl (impl q r) (impl p r))
> 
> 
> _test_impl_distributive :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_distributive =
>   testName "impl(impl(p,impl(q,r)),impl(impl(p,q),impl(p,r)))" $
>   \p q r -> impl (impl p (impl q r)) (impl (impl p q) (impl p r))

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
 & = & \bimpl(\bfalse,\band(r,s))
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

> _test_impl_and_compatible :: Test (Bool -> Bool -> Bool -> Bool -> Bool)
> _test_impl_and_compatible =
>   testName "if and(impl(p,r),impl(q,s)) then impl(and(p,q),and(r,s))" $
>   \p q r s -> if and (impl p r) (impl q s)
>     then impl (and p q) (and r s)
>     else true

::::::::::::::::::::
::::::::::::::::::::



Testing
-------

Suite:

> _test_impl ::
>   ( Boolean b, Arbitrary b, Show b, Equal b
>   ) => b -> Int -> Int -> IO ()
> _test_impl p size num = do
>   testLabel0 "Bool"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args _test_impl_false
>   runTest args _test_impl_true
>   runTest args _test_impl_reflexive
>   runTest args _test_impl_total
>   runTest args _test_impl_antecedents_commute
>   runTest args _test_impl_transitive
>   runTest args _test_impl_distributive
>   runTest args _test_impl_and_compatible

Main:

> main_impl :: IO ()
> main_impl = _test_impl (true :: Bool) 20 100
