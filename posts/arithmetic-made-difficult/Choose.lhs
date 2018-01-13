---
title: Choose
author: nbloomf
date: 2017-04-15
tags: arithmetic-made-difficult, literate-haskell
slug: choose
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Choose
>   ( choose, _test_choose, main_choose
>   ) where
>
> import Testing
> import Booleans
> import NaturalNumbers
> import DoubleNaturalRecursion
> import Plus
> import LessThanOrEqualTo

Today we'll define the binomial coefficient operator, $\nchoose$.

<div class="result">
<div class="defn"><p>
Define $\delta : \nats \rightarrow \nats$ by $$\delta(k) = \bif{\iszero(k)}{\next(\zero)}{\zero},$$ $\psi : \nats \rightarrow \nats$ by $$\psi(m) = \next(\zero),$$ and $\chi : \nats \times \nats \times \nats$ by $$\chi(t,a,b) = \nplus(a,b).$$ Now define $\nchoose : \nats \times \nats \rightarrow \nats$ by $$\nchoose = \dnatrec{\delta}{\psi}{\chi}.$$

In Haskell:

> choose :: (Natural n) => n -> n -> n
> choose = dnaturalRec delta (const (next zero)) chi
>   where
>     delta k = if isZero k then next zero else zero
>     chi _ a b = plus a b

</p></div>
</div>

Because $\nchoose$ is implemented in terms of double natural recursion, it is the unique solution to a system of equations.

<div class="result">
<div class="corollary">
$\nchoose$ is the unique solution $f : \nats \times \nats \rightarrow \nats$ to the following system of functional equations for all $n,k \in \nats$.
$$\left\{\begin{array}{l}
 f(\zero,k) = \bif{\iszero(k)}{\next(\zero)}{\zero} \\
 f(\next(n),\zero) = \next(\zero) \\
 f(\next(n),\next(k)) = \nplus(f(n,k),f(n,\next(k))).
\end{array}\right.$$
</div>

<div class="test"><p>

> _test_choose_zero_nat :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_choose_zero_nat _ =
>   testName "choose(0,k) == if(isZero(k),next(zero),zero)" $
>   \k -> if isZero k
>     then eq (choose zero k) (next zero)
>     else eq (choose zero k) zero
> 
> 
> _test_choose_next_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_choose_next_zero _ =
>   testName "choose(next(n),0) == 1" $
>   \n -> eq (choose (next n) zero) (next zero)
> 
> 
> _test_choose_next_next :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_choose_next_next _ =
>   testName "choose(next(n),next(k)) == plus(choose(n,next(k)),choose(n,k))" $
>   \n k -> eq
>     (choose (next n) (next k))
>     (plus (choose n (next k)) (choose n k))

</p></div>
</div>

We can show that $\nchoose$ satisfies the usual properties of binomial coefficients. First, if $k$ is large enough then $\nchoose(n,k) = \zero$.

<div class="result">
<div class="thm">
Let $n,k \in \nats$. If $\nleq(\next(n),k) = \btrue$, then $\nchoose(n,k) = \zero$.
</div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$, note that if $\nleq(\next(n),k) = \btrue$ then $k \neq \zero$. Then we have
$$\begin{eqnarray*}
 &   & \nchoose(n,k) \\
 & = & \nchoose(\zero,k) \\
 & = & \bif{\iszero(k)}{\next(\zero)}{\zero} \\
 & = & \zero
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $n$. Suppose further that we have $\nleq(\next(\next(n)),k) = \btrue$. Now $$k = \nplus(\next(\next(n)),u) = \next(\nplus(\next(n),u))$$ for some $u \in \nats$. Letting $m = \nplus(\next(n),u)$, note that $k = \next(m)$ and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\next(\next(n)),k) \\
 & = & \nleq(\next(\next(n)),\next(m)) \\
 & = & \nleq(\next(n),m).
\end{eqnarray*}$$
Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \nchoose(\next(\next(n)),k) \\
 & = & \nchoose(\next(\next(n)),\next(m)) \\
 & = & \nplus(\nchoose(\next(n),m),\nchoose(\next(n),\next(m))) \\
 & = & \nplus(\zero,\zero) \\
 & = & \zero
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_choose_big_k :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_choose_big_k _ =
>   testName "leq(next(n),k) ==> choose(n,k) == 0" $
>   \n k -> if leq (next n) k
>     then eq (choose n k) zero
>     else True

</p></div>
</div>

The special cases:

<div class="result">
<div class="thm">
For all $n \in \nats$, we have the following.

1. $\nchoose(n,\zero) = \next(\zero)$.
2. $\nchoose(n,n) = \next(\zero)$.
</div>

<div class="proof"><p>
1. We have two possibilities for $n$. If $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \nchoose(n,\zero) \\
 & = & \nchoose(\zero,\zero) \\
 & = & \bif{\iszero(\zero)}{\next(\zero)}{\zero} \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed. If $n = \next(m)$ for some $m$, we have
$$\begin{eqnarray*}
 &   & \nchoose(n,\zero) \\
 & = & \nchoose(\next(m),\zero) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \nchoose(n,n) \\
 & = & \nchoose(\zero,\zero) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n \in \nats$. Note that $\nleq(\next(n),\next(n)) = \btrue$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),\next(n)) \\
 & = & \nplus(\nchoose(n,n),\nchoose(n,\next(n))) \\
 & = & \nplus(\next(\zero),\zero) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_choose_nat_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_choose_nat_zero _ =
>   testName "choose(n,zero) == 1" $
>   \n -> eq (choose n zero) (next zero)
> 
> 
> _test_choose_equal_args :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_choose_equal_args _ =
>   testName "choose(n,n) == 1" $
>   \n -> eq (choose n n) (next zero)

</p></div>
</div>

$\nchoose$ is kind of symmetric:

<div class="result">
<div class="thm">
Let $n \in \nats$, and suppose $n = \nplus(k,m)$. Then $$\nchoose(n,k) = \nchoose(n,m).$$
</div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$, note that $k = m = \zero$. Then we have $\nchoose(n,k) = \nchoose(n,m)$ as needed. For the inductive step, suppose the equality holds for some $n$. Say $\next(n) = \nplus(k,m)$. We now consider two possibilities for $k$. If $k = \zero$, we have $m = \next(n)$, so that
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),k) \\
 & = & \nchoose(\next(n),\zero) \\
 & = & \next(\zero) \\
 & = & \nchoose(\next(n),\next(n)) \\
 & = & \nchoose(\next(n),m)
\end{eqnarray*}$$
as needed. Suppose then that $k = \next(v)$. We now consider two possibilities for $m$. If $m = \zero$, then $\next(n) = k$ and we have
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),k) \\
 & = & \nchoose(\next(n),\next(n)) \\
 & = & \next(\zero) \\
 & = & \nchoose(\next(n),\zero) \\
 & = & \nchoose(\next(n),m)
\end{eqnarray*}$$
as needed. Suppose then that $m = \next(u)$. Note that
$$\begin{eqnarray*}
 &   & \next(n) \\
 & = & \nplus(k,m) \\
 & = & \nplus(\next(v),m) \\
 & = & \next(\nplus(v,m))
\end{eqnarray*}$$
so that $n = \nplus(v,m)$, and similarly
$$\begin{eqnarray*}
 &   & \next(n) \\
 & = & \nplus(k,m) \\
 & = & \nplus(k,\next(u)) \\
 & = & \next(\nplus(k,u))
\end{eqnarray*}$$
so that $n = \nplus(k,u)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),k) \\
 & = & \nchoose(\next(n),\next(v)) \\
 & = & \nplus(\nchoose(n,v),\nchoose(n,\next(v))) \\
 & = & \nplus(\nchoose(n,m),\nchoose(n,k)) \\
 & = & \nplus(\nchoose(n,\next(u)),\nchoose(n,u)) \\
 & = & \nplus(\nchoose(n,u),\nchoose(n,\next(u))) \\
 & = & \nplus(\next(n),\next(u)) \\
 & = & \nplus(\next(n),m)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_choose_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_choose_plus _ =
>   testName "choose(plus(a,b),a) == choose(plus(a,b),b)" $
>   \a b -> eq (choose (plus a b) a) (choose (plus a b) b)

</p></div>
</div>


Testing
-------

Suite:

> _test_choose ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_choose n maxSize numCases = do
>   testLabel1 "choose" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_choose_zero_nat n)
>   runTest args (_test_choose_next_zero n)
>   runTest args (_test_choose_next_next n)
>   runTest args (_test_choose_big_k n)
>   runTest args (_test_choose_nat_zero n)
>   runTest args (_test_choose_equal_args n)
>   runTest args (_test_choose_plus n)

Main:

> main_choose :: IO ()
> main_choose = do
>   _test_choose (zero :: Unary) 10 50
