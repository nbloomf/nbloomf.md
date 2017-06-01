---
title: Choose
author: nbloomf
date: 2017-04-15
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE ScopedTypeVariables #-}
> module Choose
>   ( choose, _test_choose, main_choose
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import LessThanOrEqualTo
> 
> import Prelude ()
> import Test.QuickCheck hiding (choose)

Today we'll define the binomial coefficient operator, $\nchoose$.

<div class="result">
<div class="defn"><p>
Define mappings $\varphi : \nats \times \nats \rightarrow \nats$ by $$\varphi(a,b) = \bif{\iszero(a)}{\next(\zero)}{\zero},$$ $\omega : \nats \times \nats \rightarrow \nats \times \nats$ by $$\omega(a,b) = (\prev(a),a),$$ and $\chi : \nats \times \nats \rightarrow \nats^{\nats \times \nats} \rightarrow \nats$ by $$\chi((a,b),f) = \bif{\iszero(b)}{\next(\zero)}{\nplus(f(b,\zero),f(a,\zero))}.$$ We then define $\nchoose : \nats \times \nats \rightarrow \nats$ by $$\nchoose(n,k) = \mutrec{\varphi}{\omega}{\chi}(n)(k,\zero).$$
</p></div>
</div>

We can implement $\nchoose$ using the definition:

> choose' :: (Natural n) => n -> n -> n
> choose' n k = mutatingRec phi omega chi n (k,zero)
>   where
>     phi :: (Natural n) => (n,n) -> n
>     phi (a,_) = if isZero a
>       then next zero
>       else zero
> 
>     omega :: (Natural n) => (n,n) -> (n,n)
>     omega (a,_) = (prev a, a)
> 
>     chi :: (Natural n) => (n,n) -> ((n,n) -> n) -> n
>     chi (a,b) f = if isZero b
>       then next zero
>       else plus (f (b,zero)) (f (a,zero))

The following theorem suggests a more straightforward implementation.

<div class="result">
<div class="thm">
We have the following.

1. $\nchoose(\zero,k) = \bif{\iszero(k)}{\next(\zero)}{\zero}$.
2. $\nchoose(\next(n),\zero) = \next(\zero)$.
3. $\nchoose(\next(n),\next(k)) = \nplus(\nchoose(n,\next(k)),\nchoose(n,k))$.
</div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \nchoose(\zero,k) \\
 & = & \mutrec{\varphi}{\omega}{\chi}(\zero)(k,\zero) \\
 & = & \varphi(k,\zero) \\
 & = & \bif{\iszero(k)}{\next(\zero)}{\zero}
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),\zero) \\
 & = & \mutrec{\varphi}{\omega}{\chi}(\next(n))(\zero,\zero) \\
 & = & \chi(\omega(\zero,\zero),\mutrec{\varphi}{\omega}{\chi}(n)) \\
 & = & \chi((\zero,\zero),\mutrec{\varphi}{\omega}{\chi}(n)) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \nchoose(\next(n),\next(k)) \\
 & = & \mutrec{\varphi}{\omega}{\chi}(\next(n))(\next(k),\zero) \\
 & = & \chi(\omega(\next(k),\zero),\mutrec{\varphi}{\omega}{\chi}(n)) \\
 & = & \chi((k,\next(k)),\mutrec{\varphi}{\omega}{\chi}(n)) \\
 & = & \nplus(\mutrec{\varphi}{\omega}{\chi}(n)(\next(k),\zero),\mutrec{\varphi}{\omega}{\chi}(n)(k,\zero)) \\
 & = & \nplus(\nchoose(n,\next(k)),\nchoose(n,k))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> choose :: (Natural n) => n -> n -> n
> choose n k = case natShape n of
>   Zero   -> if isZero k then next zero else zero
>   Next m -> case natShape k of
>     Zero   -> next zero
>     Next t -> plus (choose m k) (choose m t)

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
</div>


Implementation and Testing
--------------------------

Property tests:

> -- choose(n,k) == choose'(n,k)
> _test_choose_alt :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_choose_alt _ n k =
>   (choose n k) ==== (choose' n k)
> 
> 
> -- choose(0,k) == if k==0 then 0 else 1
> _test_choose_zero_left :: (Natural n)
>   => n -> Nat n -> Bool
> _test_choose_zero_left _ k =
>   if isZero k
>     then (choose zero k) ==== (next zero)
>     else (choose zero k) ==== (zero)
> 
> 
> -- choose(n,0) == 1
> _test_choose_zero_right :: (Natural n)
>   => n -> Nat n -> Bool
> _test_choose_zero_right _ n =
>   (choose n zero) ==== (next zero)
> 
> 
> -- choose(n,n) == 1
> _test_choose_equal_args :: (Natural n)
>   => n -> Nat n -> Bool
> _test_choose_equal_args _ n =
>   (choose n n) ==== (next zero)
> 
> 
> -- choose(next(n),next(k)) == plus(choose(n,next(k)),choose(n,k))
> _test_choose_plus_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_choose_plus_plus _ n k =
>   eq
>     (choose (next n) (next k))
>     (plus (choose n (next k)) (choose n k))
> 
> 
> -- leq(next(n),k) ==> choose(n,k) == 0
> _test_choose_big_k :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_choose_big_k _ n k =
>   if leq (next n) k
>     then (choose n k) ==== zero
>     else True
> 
> 
> -- choose(plus(a,b),a) == choose(plus(a,b),b)
> _test_choose_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_choose_plus _ a b =
>   (choose (plus a b) a) ==== (choose (plus a b) b)

And the suite:

> -- run all tests for choose
> _test_choose ::
>   ( TypeName n, Natural n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_choose n maxSize numCases = do
>   testLabel ("choose: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_choose_alt n)
>   runTest args (_test_choose_zero_left n)
>   runTest args (_test_choose_zero_right n)
>   runTest args (_test_choose_equal_args n)
>   runTest args (_test_choose_plus_plus n)
>   runTest args (_test_choose_big_k n)
>   runTest args (_test_choose_plus n)

And the main function:

> main_choose :: IO ()
> main_choose = do
>   _test_choose (zero :: Unary) 10 50
