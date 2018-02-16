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
[]{#def-implies}
We define $\bimpl : \bool \rightarrow \bool \rightarrow \bool$ by $$\bimpl(p,q) = \bif{p}{q}{\btrue}.$$

In Haskell:

> impl :: (Boolean b) => b -> b -> b
> impl p q = ifThenElse p q true

::::::::::::::::::::

$\bimpl$ is equivalent to an $\bor$.

:::::: theorem :::::
[]{#thm-implies-or}
For all $p,q \in \bool$, we have $$\bimpl(p,q) = \bor(\bnot(p),q).$$

::: proof ::::::::::
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,q) \\
 &     \href{@implies@#def-implies}
   = & \bif{\bfalse}{q}{\btrue} \\
 &     \href{@booleans@#cor-if-false}
   = & \btrue \\
 &     \href{@or@#thm-or-true-left}
   = & \bor(\btrue,q) \\
 &     \href{@not@#thm-not-false}
   = & \bor(\bnot(\bfalse),q)
\end{eqnarray*}$$
as needed. Suppose then that $p = \btrue$. Then
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,q) \\
 &     \href{@implies@#def-implies}
   = & \bif{\btrue}{q}{\btrue} \\
 &     \href{@booleans@#cor-if-true}
   = & q \\
 &     \href{@or@#thm-or-false-left}
   = & \bor(\bfalse,q) \\
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
[]{#thm-implies-false-hyp}
If $p \in \bool$, we have $\bimpl(\bfalse,p) = \btrue$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,p) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(\bfalse),p) \\
 &     \href{@not@#thm-not-false}
   = & \bor(\btrue,p) \\
 &     \href{@or@#thm-or-true-left}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_false_hyp :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_false_hyp _ =
>   testName "impl(false,p) == true" $
>   \p -> eq (impl false p) true

::::::::::::::::::::
::::::::::::::::::::

$\bfalse$ interacts with $\bimpl$ in the right argument.

:::::: theorem :::::
[]{#thm-implies-false-conc}
If $p \in \bool$, we have $\bimpl(p,\bfalse) = \bnot(p)$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\bfalse) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(p),\bfalse) \\
 &     \href{@or@#thm-or-false-right}
   = & \bnot(p)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_false_conc :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_false_conc _ =
>   testName "impl(p,false) == not(p)" $
>   \p -> eq (impl p false) (not p)

::::::::::::::::::::
::::::::::::::::::::

$\btrue$ is left-neutral.

:::::: theorem :::::
[]{#thm-implies-true-hyp}
For all $p \in \bool$ we have $\bimpl(\btrue,p) = p$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,p) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(\btrue),p) \\
 &     \href{@not@#thm-not-true}
   = & \bor(\bfalse,p) \\
 &     \href{@or@#thm-or-false-left}
   = & p
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_true_hyp :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_true_hyp _ =
>   testName "impl(true,p) == p" $
>   \p -> eq (impl true p) p

::::::::::::::::::::
::::::::::::::::::::

$\btrue$ is right-absorptive.

:::::: theorem :::::
[]{#thm-implies-true-conc}
If $p \in \bool$, we have $\bimpl(p,\btrue) = \btrue$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\btrue) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(p),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_true_conc :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_impl_true_conc _ =
>   testName "impl(p,true) == true" $
>   \p -> eq (impl p true) true

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ is... idemp-constant? Not sure what to call this.

:::::: theorem :::::
[]{#thm-implies-self}
If $p \in \bool$ we have $\bimpl(p,p) = \btrue$.

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,\btrue) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(\btrue),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl{\bfalse,\bfalse} \\
 &     \href{@implies@#thm-implies-false-hyp}
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
[]{#thm-implies-antisymmetric}
For all $p,q \in \bool$ we have $\bor(\bimpl(p,q),\bimpl(q,p))$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bor(\bimpl(p,q),\bimpl(q,p)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bor(\bnot(p),q),\bimpl(q,p)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bor(\bnot(p),q),\bor(\bnot(q),p)) \\
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
[]{#thm-implies-left-commutative}
For all $p,q,r \in \bool$ we have $$\bimpl(p,\bimpl(q,r)) = \bimpl(q,\bimpl(p,r)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\bimpl(q,r)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(p),\bimpl(q,r)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(p),\bor(\bnot(q),r)) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bor(\bnot(p),\bnot(q)),r) \\
 &     \href{@or@#thm-or-commutative}
   = & \bor(\bor(\bnot(q),\bnot(p)),r) \\
 &     \href{@or@#thm-or-associative}
   = & \bor(\bnot(q),\bor(\bnot(p),r)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(q),\bimpl(p,r)) \\
 &     \href{@implies@#thm-implies-or}
   = & \bimpl(q,\bimpl(p,r))
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
[]{#thm-implies-transitive}
For all $p,q,r \in \bool$ we have $$\bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))).$$

::: proof ::::::::::
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))) \\
 &     \let{p = \bfalse}
   = & \bimpl(\bimpl(\bfalse,q),\bimpl(\bimpl(q,r),\bimpl(\bfalse,r))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\btrue,\bimpl(\bimpl(q,r),\bimpl(\bfalse,r))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\btrue,\bimpl(\bimpl(q,r),\btrue)) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\bimpl(q,r),\btrue) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(\bimpl(q,r)),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))) \\
 &     \let{p = \btrue}
   = & \bimpl(\bimpl(\btrue,q),\bimpl(\bimpl(q,r),\bimpl(\btrue,r))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(q,\bimpl(\bimpl(q,r),\bimpl(\btrue,r))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(q,\bimpl(\bimpl(q,r),r)) \\
 &     \href{@implies@#thm-implies-left-commutative}
   = & \bimpl(\bimpl(q,r),\bimpl(q,r)) \\
 &     \href{@implies@#thm-implies-self}
   = & \btrue
\end{eqnarray*}$$
as claimed.
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
[]{#thm-implies-distribute}
For all $p,q,r \in \bool$ we have $$\bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))).$$

::: proof ::::::::::
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 &     \let{p = \bfalse}
   = & \bimpl(\bimpl(\bfalse,\bimpl(q,r)),\bimpl(\bimpl(\bfalse,q),\bimpl(\bfalse,r))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\btrue,\bimpl(\bimpl(\bfalse,q),\bimpl(\bfalse,r))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\btrue,\bimpl(\btrue,\bimpl(\bfalse,r))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\btrue,\bimpl(\btrue,\btrue)) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\btrue,\btrue) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \btrue
\end{eqnarray*}$$
Suppose instead that $p = \btrue$. Now
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 &     \let{p = \btrue}
   = & \bimpl(\bimpl(\btrue,\bimpl(q,r)),\bimpl(\bimpl(\btrue,q),\bimpl(\btrue,r))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\bimpl(q,r),\bimpl(\bimpl(\btrue,q),\bimpl(\btrue,r))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\bimpl(q,r),\bimpl(q,\bimpl(\btrue,r))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\bimpl(q,r),\bimpl(q,r)) \\
 &     \href{@implies@#thm-implies-self}
   = & \btrue
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
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\band(\bimpl(p,r),\bimpl(q,s)),\bimpl(\band(p,q),\band(r,s))) \\
 &     \let{p = \bfalse}
   = & \bimpl(\band(\bimpl(\bfalse,r),\bimpl(q,s)),\bimpl(\band(\bfalse,q),\band(r,s))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\band(\btrue,\bimpl(q,s)),\bimpl(\band(\bfalse,q),\band(r,s))) \\
 &     \href{@and@#thm-and-false-left}
   = & \bimpl(\band(\btrue,\bimpl(q,s)),\bimpl(\bfalse,\band(r,s))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \bimpl(\band(\btrue,\bimpl(q,s)),\btrue) \\
 &     \href{@implies@#thm-implies-or}
   = & \bor(\bnot(\band(\btrue,\bimpl(q,s))),\btrue) \\
 &     \href{@or@#thm-or-true-right}
   = & \btrue
\end{eqnarray*}$$
as claimed. suppose $p = \btrue$. If $r = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\band(\bimpl(p,r),\bimpl(q,s)),\bimpl(\band(p,q),\band(r,s))) \\
 &     \let{p = \btrue}
   = & \bimpl(\band(\bimpl(\btrue,r),\bimpl(q,s)),\bimpl(\band(\btrue,q),\band(r,s))) \\
 &     \href{@and@#thm-and-true-left}
   = & \bimpl(\band(\bimpl(\btrue,r),\bimpl(q,s)),\bimpl(q,\band(r,s))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\band(r,\bimpl(q,s)),\bimpl(q,\band(r,s))) \\
 &     \let{r = \bfalse}
   = & \bimpl(\band(\bfalse,\bimpl(q,s)),\bimpl(q,\band(\bfalse,s))) \\
 &     \href{@and@#thm-and-false-left}
   = & \bimpl(\bfalse,\bimpl(q,\band(\bfalse,s))) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \btrue
\end{eqnarray*}$$
as claimed. If $r = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\band(\bimpl(p,r),\bimpl(q,s)),\bimpl(\band(p,q),\band(r,s))) \\
 &     \let{p = \btrue}
   = & \bimpl(\band(\bimpl(\btrue,r),\bimpl(q,s)),\bimpl(\band(\btrue,q),\band(r,s))) \\
 &     \href{@and@#thm-and-true-left}
   = & \bimpl(\band(\bimpl(\btrue,r),\bimpl(q,s)),\bimpl(q,\band(r,s))) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\band(r,\bimpl(q,s)),\bimpl(q,\band(r,s))) \\
 &     \let{r = \btrue}
   = & \bimpl(\band(\btrue,\bimpl(q,s)),\bimpl(q,\band(\btrue,s))) \\
 &     \href{@and@#thm-and-true-left}
   = & \bimpl(\bimpl(q,s),\bimpl(q,\band(\btrue,s))) \\
 &     \href{@and@#thm-and-true-left}
   = & \bimpl(\bimpl(q,s),\bimpl(q,s)) \\
 &     \href{@implies@#thm-implies-self}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_impl_and_compatible
>   :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> b -> Bool)
> _test_impl_and_compatible _ =
>   testName "if and(impl(p,r),impl(q,s)) then impl(and(p,q),and(r,s))" $
>   \p q r s -> isTrue $ ifThenElse (and (impl p r) (impl q s))
>     (impl (and p q) (and r s))
>     (true)

::::::::::::::::::::
::::::::::::::::::::

$\bimpl$ interacts with $\band$ and $\bif{\ast}{\ast}{\ast}$.

:::::: theorem :::::
Let $p,q,r \in \bool$. If $\bimpl(r,q)$, then $$\bif{\band(p,q)}{\btrue}{r} = \bif{p}{q}{r}.$$

::: proof ::::::::::
If $q = \btrue$ then
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(r,q),\beq(\bif{\band(p,q)}{\btrue}{r},\bif{p}{q}{r})) \\
 &     \let{q = \btrue}
   = & \bimpl(\bimpl(r,\btrue),\beq(\bif{\band(p,\btrue)}{\btrue}{r},\bif{p}{\btrue}{r})) \\
 &     \href{@implies@#thm-implies-true-conc}
   = & \bimpl(\btrue,\beq(\bif{\band(p,\btrue)}{\btrue}{r},\bif{p}{\btrue}{r})) \\
 &     \href{@and@#thm-and-true-right}
   = & \bimpl(\btrue,\beq(\bif{p}{\btrue}{r},\bif{p}{\btrue}{r})) \\
 &     \href{@booleans@#thm-eq-reflexive}
   = & \bimpl(\btrue,\btrue) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \btrue
\end{eqnarray*}$$
as claimed. If $q = \bfalse$ and $r = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(r,q),\beq(\bif{\band(p,q)}{\btrue}{r},\bif{p}{q}{r})) \\
 &     \let{q = \bfalse}
   = & \bimpl(\bimpl(r,\bfalse),\beq(\bif{\band(p,\bfalse)}{\btrue}{r},\bif{p}{\bfalse}{r})) \\
 &     \href{@implies@#thm-implies-false-conc}
   = & \bimpl(\bnot(r),\beq(\bif{\band(p,\bfalse)}{\btrue}{r},\bif{p}{\bfalse}{r})) \\
 &     \href{@and@#thm-and-false-right}
   = & \bimpl(\bnot(r),\beq(\bif{\bfalse}{\btrue}{r},\bif{p}{\bfalse}{r})) \\
 &     \href{@booleans@#cor-if-false}
   = & \bimpl(\bnot(r),\beq(r,\bif{p}{\bfalse}{r})) \\
 &     \let{r = \bfalse}
   = & \bimpl(\bnot(\bfalse),\beq(\bfalse,\bif{p}{\bfalse}{\bfalse})) \\
 &     \href{@not@#thm-not-false}
   = & \bimpl(\btrue,\beq(\bfalse,\bif{p}{\bfalse}{\bfalse})) \\
 &     \href{@booleans@#thm-if-same}
   = & \bimpl(\btrue,\beq(\bfalse,\bfalse)) \\
 &     \href{@booleans@#thm-eq-reflexive}
   = & \bimpl(\btrue,\btrue) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \btrue
\end{eqnarray*}$$
as claimed. And if $q = \bfalse$ and $r = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(r,q),\beq(\bif{\band(p,q)}{\btrue}{r},\bif{p}{q}{r})) \\
 &     \let{q = \bfalse}
   = & \bimpl(\bimpl(r,\bfalse),\beq(\bif{\band(p,\bfalse)}{\btrue}{r},\bif{p}{\bfalse}{r})) \\
 &     \let{r = \btrue}
   = & \bimpl(\bimpl(\btrue,\bfalse),\beq(\bif{\band(p,\bfalse)}{\btrue}{\btrue},\bif{p}{\bfalse}{\btrue})) \\
 &     \href{@implies@#thm-implies-true-hyp}
   = & \bimpl(\bfalse,\beq(\bif{\band(p,\bfalse)}{\btrue}{\btrue},\bif{p}{\bfalse}{\btrue})) \\
 &     \href{@implies@#thm-implies-false-hyp}
   = & \btrue
\end{eqnarray*}$$
as claimed.
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
>   runTest args (_test_impl_false_hyp p)
>   runTest args (_test_impl_false_conc p)
>   runTest args (_test_impl_true_hyp p)
>   runTest args (_test_impl_true_conc p)
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
