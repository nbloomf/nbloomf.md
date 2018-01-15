---
title: Find Smallest
author: nbloomf
date: 2017-12-29
tags: arithmetic-made-difficult, literate-haskell
slug: findsmallest
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module FindSmallest (
>   findSmallest, _test_findSmallest, main_findSmallest
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import LessThanOrEqualTo

The Well-Ordering Principle on $\nats$ gives a sufficient condition under which a natural number minimal with respect to a given property must exist; namely, that the set of all natural numbers with that property is not empty. WOP can come in really handy when we want to show that, say, the smallest number $k$ with property *foo* exists, and reason about it. Unfortunately, WOP alone is nonconstructive -- it tells us nothing about how to actually *find* anything. Today we'll establish a weak constructive form of WOP.

More precisely, given a predicate $\sigma : \nats \rightarrow \bool$ and two natural numbers $k$ and $n$, we'll define an operator $\Theta$ such that $\Theta(\next(n),k)$ is the *smallest* number $t$ between $k$ and $\nplus(k,n)$ such that $\sigma(t) = \btrue$, if any such number exists, and $\ast$ otherwise.

:::::: definition ::
Let $\sigma : \nats \rightarrow \bool$. Define $\varphi : \nats \rightarrow 1 + \nats$ by $$\varphi(k) = \lft(\ast),$$ $\beta : \nats \times \nats \rightarrow \bool$ by $$\beta(n,k) = \sigma(k),$$ $\psi : \nats \times \nats \rightarrow 1 + \nats$ by $$\psi(n,k) = \rgt(k),$$ and $\omega : \nats \times \nats \rightarrow \nats$ by $$\omega(n,k) = \next(k).$$ We then define $$\findsmallest{} : \bool^\nats \rightarrow \nats \times \nats \rightarrow 1 + \nats$$ by $$\findsmallest{\sigma}(n,k) = \bailrec{\varphi}{\beta}{\psi}{\omega}(n,k).$$

In Haskell:

> findSmallest :: (Natural n) => (n -> Bool) -> n -> n -> Either () n
> findSmallest sigma = bailoutRec phi beta psi omega
>   where
>     phi k = lft ()
>     beta _ k = sigma k
>     psi _ k = rgt k
>     omega _ k = next k

::::::::::::::::::::
::::::::::::::::::::

Because $\findsmallest{\sigma}$ is defined in terms of bailout recursion, it is the unique solution to a system of functional equations.

<div class="cor"><p>
Let $\sigma : \nats \rightarrow \bool$ be a map. Then $\findsmallest{\sigma} : \nats \times \nats \rightarrow 1 + \nats$ is the unique solution $f : \nats \times \nats \rightarrow 1 + \nats$ to the following system of equations for all $n,k \in \nats$.
$$\left\{\begin{array}{l}
 f(\zero,k) = \lft(\ast) \\
 f(\next(n),k) = \bif{\sigma(k)}{\rgt(k)}{f(n,\next(k))}
\end{array}\right.$$
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_zero_left :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> Bool)
> _test_findSmallest_zero_left _ =
>   testName "findSmallest(sigma)(0,k) == lft(*)" $
>   \sigma k -> eq (findSmallest sigma zero k) (lft ())
> 
> 
> _test_findSmallest_next_left :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> Bool)
> _test_findSmallest_next_left _ =
>   testName "findSmallest(sigma)(next(n),k) == if(sigma(k),rgt(k),findSmallest(sigma)(n,next(k)))" $
>   \sigma n k -> eq
>     (findSmallest sigma (next n) k)
>     (if sigma k then rgt k else findSmallest sigma n (next k))

::::::::::::::::::::
::::::::::::::::::::

First, if $\findsmallest{\sigma}$ returns a result $\rgt(t)$, then $t$ satisfies $\sigma$.

:::::: theorem :::::
Let $\sigma : \nats \rightarrow \bool$, with $n,k,t \in \nats$. If $\findsmallest{\sigma}(n,k) = \rgt(t)$, then $\sigma(t) = \btrue$.
::::::::::::::::::::

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$, note that $$\findsmallest{\sigma}(\zero,k) = \lft(\ast),$$ so the implication holds vacuously. For the inductive step, suppose we have $n$ such that for all $k$ and $t$, if $\findsmallest{\sigma}(n,k) = \rgt(t)$ then $\sigma(t) = \btrue$. Suppose further that $\findsmallest{\sigma}(\next(n),k) = \rgt(t)$. Now we have $$\findsmallest{\sigma}(\next(n),k) = \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(n,\next(k))}.$$ We have two possibilities. If $\sigma(k) = \btrue$, then $$\findsmallest{\sigma}(n,k) = \rgt(k),$$ with $\sigma(k) = \btrue$ as needed. If $\sigma(k) = \bfalse,$ we have $$\rgt(t) = \findsmallest{\sigma}(\next(n),k) = \findsmallest{\sigma}(n,\next(k)),$$ and by the inductive hypothesis, $\sigma(t) = \btrue$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_satisfies :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> Bool)
> _test_findSmallest_satisfies _ =
>   testName "if findSmallest(sigma)(n,k) == rgt(t) then sigma(t) == true" $
>   \sigma n k -> case findSmallest sigma n k of
>     Right t -> eq (sigma t) true
>     Left () -> true

::::::::::::::::::::
::::::::::::::::::::

Next, if $\findsmallest{\sigma}(\next(n),k)$ returns a result $\rgt(t)$, then $t$ is bounded; specifically, $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$.

:::::: theorem :::::
If $\findsmallest{\sigma}(\next(n),k) = \rgt(t)$, then $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$.
::::::::::::::::::::

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$, if $\findsmallest{\sigma}(\next(n),k) = \rgt(t)$ we have
$$\begin{eqnarray*}
 &   & \findsmallest{\sigma}(\next(\zero),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\zero,\next(k))} \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\lft(\ast)}.
\end{eqnarray*}$$
In particular, we must have $\sigma(k) = \btrue$ and $t = k$. Thus $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$ as needed.

For the inductive step, suppose the implication holds for all $k$ and $t$ for some $n$, and suppose further that $\findsmallest{\sigma}(\next(\next(n)),k) = \rgt(t)$. Now
$$\begin{eqnarray*}
 &   & \rgt(t) \\
 & = & \findsmallest{\sigma}(\next(\next(n)),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\next(n),\next(k))}.
\end{eqnarray*}$$
We have two possibilities. If $\sigma(k) = \btrue$, then $\rgt(t) = \rgt(k)$, so that $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$ as needed. If $\sigma(k) = \bfalse$, we have $\rgt(t) = \findsmallest{\sigma}(\next(n),\next(k))$. By the inductive hypothesis, we have $\nleq(\next(k),t)$ and $\nleq(t,\nplus(\next(n),\next(k))$. By transitivity we thus have $\nleq(k,t)$ and $\nleq(t,\nplus(\next(\next(n)),k)$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_bounded :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> Bool)
> _test_findSmallest_bounded _ =
>   testName "if findSmallest(sigma)(next(n),k) == rgt(t) then leq(k,t) and leq(t,plus(n,k))" $
>   \sigma n k -> case findSmallest sigma (next n) k of
>     Right t -> and (leq k t) (leq t (plus n k))
>     Left () -> true

::::::::::::::::::::
::::::::::::::::::::

$\findsmallest{\sigma}(\next(n),k)$ returns $\lft(\ast)$ if and only if $\sigma$ is false for all $u$ between $k$ and $\nplus(n,k)$.

:::::: theorem :::::
Let $\sigma : \nats \rightarrow \bool$ and $n,k \in \nats$. Then $\findsmallest{\sigma}(\next(n),k) = \lft(\ast)$ if and only if $\sigma(t) = \bfalse$ for all $t$ with $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$.
::::::::::::::::::::

::: proof ::::::::::
We prove the "only if" direction by induction on $n$. For the base case $n = \zero$, suppose $\findsmallest{\sigma}(\next(\zero),k) = \lft(\ast)$. Expanding, we have
$$\begin{eqnarray*}
 &   & \lft(\ast) \\
 & = & \findsmallest{\sigma}(\next(\zero),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\zero,\next(k))}
 & = & \bif{\sigma(k)}{\rgt(k)}{\lft(\ast)}.
\end{eqnarray*}$$
Thus $\sigma(k) = \bfalse$. Now if $\nleq(k,t)$ and $\nleq(t,\nplus(\zero,k))$, we have $t = k$ by antisymmetry, and thus $\sigma(t) = \bfalse$ for all $\nleq(k,t)$ and $\nleq(t,\nplus(n,k))$ as needed. For the inductive step, suppose the implication holds for all $k$ for some $n$, and suppose further that $\findsmallest{\sigma}(\next(\next(n)),k) = \lft(\ast)$. Expanding, we have
$$\begin{eqnarray*}
 &   & \lft(\ast) \\
 & = & \findsmallest{\sigma}(\next(\next(n)),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\next(n),\next(k))}. \\
\end{eqnarray*}$$
Now we must have $\sigma(k) = \bfalse$, and moreover $\findsmallest{\sigma}(\next(n),\next(k)) = \lft(\ast)$. By the inductive hypothesis, we have $\sigma(t) = \bfalse$ whenever $\nleq(\next(k),t)$ and $\nleq(t,\nplus(\next(n),\next(k))$; thus $\sigma(t) = \bfalse$ whenever $\nleq(k,t)$ and $\nleq(t,\nplus(\next(\next(n)),k)$ as needed.

We also prove the "if" direction by induction on $n$. For the base case $n = \zero$, suppose $\sigma(t) = \bfalse$ when $\nleq(k,t)$ and $\nleq(t,\nplus(\zero,k))$; by antisymmetry, we have $\sigma(k) = \bfalse$, and thus
$$\begin{eqnarray*}
 &   & \findsmallest{\sigma}(\next(\zero),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\zero,k)} \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\lft(\ast)} \\
 & = & \bif{\bfalse}{\rgt(k)}{\lft(\ast)} \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $k$ for some $n$, and suppose further that $\sigma(t) = \bfalse$ whenever $\nleq(k,t)$ and $\nleq(t,\nplus(\next(n),k)$. Then we have $\sigma(k) = \bfalse$, and we also have $\sigma(t) = \bfalse$ whenever $\nleq(\next(k),t)$ and $\nleq(t,\nplus(n,\next(k))$, and by the inductive hypothesis, $\findsmallest{\sigma}(\next(n),\next(k)) = \lft(\ast)$. Now
$$\begin{eqnarray*}
 &   & \findsmallest{\sigma}(\next(\next(n)),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\next(n),\next(k))} \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\lft(\ast)} \\
 & = & \bif{\bfalse}{\rgt(k)}{\lft(\ast)} \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_return_lft :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> n -> Bool)
> _test_findSmallest_return_lft _ =
>   testName "if eq(findSmallest(sigma)(next(n),k),lft(*)) and leq(k,t) and leq(t,plus(n,k)) then eq(sigma(t),false)" $
>   \sigma n k t -> if and (leq k t) (leq t (plus n k))
>     then if eq (findSmallest sigma (next n) k) (lft ())
>       then eq (sigma t) false
>       else true
>     else true

::::::::::::::::::::
::::::::::::::::::::

If $\findsmallest{\sigma}(n,k)$ returns a value, then $\findsmallest{\sigma}(t,k)$ does not, where $t$ is the difference between $k$ and the returned value.

:::::: theorem :::::
If $\findsmallest{\sigma}(n,k) = \rgt(\nplus(k,\next(t)))$, then $\findsmallest{\sigma}(t,k) = \lft(\ast)$.
::::::::::::::::::::

::: proof ::::::::::
We proceed by induction on $t$. For the base case $t = \zero$, note that $$\findsmallest{\sigma}(\zero,k) = \lft(\ast),$$ so the implication holds regardless of $n$ and $k$. For the inductive step, suppose the implication holds for all $n$ and $k$ for some $t$, and suppose further that $$\findsmallest{\sigma}(n,k) = \rgt(\nplus(k,\next(\next(t)))).$$ Now we must have $n = \next(m)$ for some $m$, and moreover
$$\begin{eqnarray*}
 &   & \rgt(\nplus(\next(k),\next(t))) \\
 & = & \rgt(\nplus(k,\next(\next(t)))) \\
 & = & \findsmallest{\sigma}(\next(m),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(m,\next(k))} \\
\end{eqnarray*}$$
Note that $\sigma(k)$ cannot be $\btrue$, as in this case we have $k = \nplus(k,\next(\next(t)))$. So we have $\sigma(k) = \bfalse$ and
$$\begin{eqnarray*}
 &   & \rgt(\nplus(\next(k),\next(t))) \\
 & = & \findsmallest{\sigma}(m,\next(k)).
\end{eqnarray*}$$
By the inductive hypothesis, we have $\findsmallest{\sigma}(t,\next(k)) = \lft(\ast)$, and thus
$$\begin{eqnarray*}
 &   & \findsmallest{\sigma}(\next(t),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(t,\next(k))} \\
 & = & \findsmallest{\sigma}(t,\next(k)) \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_value_lft :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> n -> Bool)
> _test_findSmallest_value_lft _ =
>   testName "if findSmallest(sigma)(n,k) == rgt(plus(k,next(t))) then findSmallest(sigma)(t,k) = lft(*)" $
>   \sigma n k t -> if eq (findSmallest sigma n k) (rgt (plus k (next t)))
>     then eq (findSmallest sigma t k) (lft ())
>     else true

::::::::::::::::::::
::::::::::::::::::::

Finally, $\findsmallest{\sigma}$ returns a least value.

:::::: theorem :::::
If $\findsmallest{\sigma}(\next(n),k) = \rgt(t)$, and if $u \in \nats$ such that $\sigma(u) = \btrue$, $\nleq(k,u)$, and $\nleq(u,\nplus(n,k))$, then $\nleq(t,u)$.
::::::::::::::::::::

::: proof ::::::::::
We proceed by induction on $n$. For the base case $n = \zero$, suppose
$$\begin{eqnarray*}
 &   & \rgt(t) \\
 & = & \findsmallest{\sigma}(\next(\zero),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\lft(\ast)}. \\
\end{eqnarray*}$$
We must have $\sigma(k) = \btrue$ and thus $k = t$. Then we have $\nleq(t,u)$ whenever $\nleq(k,u)$ as needed.

For the inductive step, suppose the implication holds for all $k$, $t$, and $u$ for some $n$, and suppose further that $\findsmallest{\sigma}(\next(\next(n)),k) = \rgt(t)$. Now $t = \nplus(k,m)$ for some $m$ since $\nleq(k,t)$. We have
$$\begin{eqnarray*}
 &   & \rgt(\nplus(k,m)) \\
 & = & \rgt(t) \\
 & = & \findsmallest{\sigma}(\next(\next(n)),k) \\
 & = & \bif{\sigma(k)}{\rgt(k)}{\findsmallest{\sigma}(\next(n),\next(k))}.
\end{eqnarray*}$$
If $\sigma(k) = \btrue$, then $t = k$, and we again have $\nleq(t,u)$ as needed. If instead $\sigma(k) = \bfalse$, we have $$\rgt(t) = \findsmallest{\sigma}(\next(n),\next(k)).$$ By the inductive hypothesis, if $\sigma(u) = \btrue$ and $\nleq(\next(k),u)$ and $\nleq(u,\nplus(n,\next(k))$, then $\nleq(t,u)$. Suppose $\sigma(u) = \btrue$, $\nleq(k,u)$, and $\nleq(u,\nplus(\next(n),k))$. Since $\sigma(k) = \bfalse$, we have $\nleq(\next(k),u)$, so by the inductive hypothesis, $\nleq(t,u)$ as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_findSmallest_minimal :: (Natural n, Equal n)
>   => n -> Test ((n -> Bool) -> n -> n -> n -> n -> Bool)
> _test_findSmallest_minimal _ =
>   testName "if findSmallest(sigma)(next(n),k) == rgt(t) and sigma(u) and leq(k,u) and leq(u,plus(n,k) then leq(t,u)" $
>   \sigma n k t u -> case findSmallest sigma (next n) k of
>     Right t -> if and (sigma u) (and (leq k u) (leq u (plus n k)))
>       then leq t u
>       else true
>     Left () -> true

::::::::::::::::::::
::::::::::::::::::::

To summarize:

:::::: corollary :::
Let $\sigma : \nats \rightarrow \bool$ and $n,k \in \nats$.

1. If $\findsmallest{\sigma}(\next(n),k) = \rgt(t)$, then $\sigma(t)$, $\nleq(k,t)$, and $\nleq(t,\nplus(n,k))$, and if $u \in \nats$ such that $\sigma(u)$, $\nleq(k,u)$, and $\nleq(u,\nplus(n,k))$, then $\nleq(t,u)$.
2. If $\findsmallest{\sigma}(\next(n),k) = \lft(\ast)$, then there does not exist $u \in \nats$ such that $\sigma(u)$, $\nleq(k,u)$, and $\nleq(u,\nplus(n,k))$.
::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_findSmallest ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, CoArbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_findSmallest n maxSize numCases = do
>   testLabel1 "findSmallest" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_findSmallest_zero_left n)
>   runTest args (_test_findSmallest_next_left n)
>   runTest args (_test_findSmallest_satisfies n)
>   runTest args (_test_findSmallest_bounded n)
>   runTest args (_test_findSmallest_return_lft n)
>   runTest args (_test_findSmallest_value_lft n)
>   runTest args (_test_findSmallest_minimal n)

Main:

> main_findSmallest :: IO ()
> main_findSmallest = do
>   _test_findSmallest (zero :: Unary) 50 100
