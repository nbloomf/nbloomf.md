---
title: Mutating Recursion
author: nbloomf
date: 2014-05-22
tags: arithmetic-made-difficult, literate-haskell
---

> module MutatingRecursion
>   ( mutRec
>   ) where
> 
> import Unary

Note that both simple recursion and bailout recursion produce functions with type $$\nats \times A \rightarrow B;$$ we can call that $A$ argument the *parameter*. Now simple and bailout recursion use the parameter in different ways. Simple recursion is only allowed to change $A$ "outside" the recursive call, while bailout recursion can only change $A$ "inside" the recursive call. These restrictions were necessary so that simple and bailout recursion would have tail-recursive implementations. But there are times when we will want a recursive function with signature $\nats \times A \rightarrow B$ that can change its $A$ parameter both inside and outside the recursion.

For this situation we introduce yet another recursion operator on $\nats$, which we'll call *mutating recursion*.

<div class="result">
<div class="thm">
Let $A$ and $B$ be sets, and suppose we have mappings $$\varphi : A \rightarrow B,$$ $$\omega : A \rightarrow A,$$ and $$\chi : A \times B^A \rightarrow B.$$ There is a unique map $\Theta : \nats \rightarrow A \rightarrow B$ such that $$\Theta(\zero)(a) = \varphi(a)$$ and $$\Theta(\next(n))(a) = \chi(\omega(a),\Theta(n)).$$ We will call such functions *mutating recursive*, and denote this $\Theta$ by $\mutrec{\varphi}{\omega}{\chi}$.
</div>

<div class="proof">
Define $\Omega : B^A \rightarrow B^A$ by $$\Omega(f)(a) = \chi(\omega(a),f).$$ Now $(B^A, \varphi, \Omega)$ is an inductive set; define $\Theta = \natrec{\varphi}{\Omega}$. Then $\Theta$ is unique such that
$$\begin{eqnarray*}
 &   & \Theta(\zero)(a) \\
 & = & \natrec{\varphi}{\Omega}(\zero)(a) \\
 & = & \varphi(a)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \Theta(\next(n))(a) \\
 & = & \natrec{\varphi}{\Omega}(\next(n))(a) \\
 & = & \Omega(\natrec{\varphi}{\Omega}(n))(a) \\
 & = & \chi(\omega(a),\natrec{\varphi}{\Omega}(n)) \\
 & = & \chi(\omega(a),\Theta(n))
\end{eqnarray*}$$
as claimed.
</div>
</div>


Implementation
--------------

As usual we now want to implement $\mutrec{\ast}{\ast}{\ast}$ in software, and there are a couple of ways to go about this. First, the signature.

> mutRec, mutRec'
>   :: (a -> b)
>   -> (a -> a)
>   -> (a -> (a -> b) -> b)
>   -> Unary
>   -> a
>   -> b

There's the naive way:

> mutRec phi omega chi =
>   let
>     theta n a = case n of
>       Z   -> phi a
>       N m -> chi (omega a) (theta m)
> 
>   in theta

And there's the definition from the proof:

> mutRec' phi omega chi =
>   let w f a = chi (omega a) f in
>   natRec phi w

The naive implementation of mutating recursion is not tail recursive, and I think (without proof) that no truly tail recursive implementation exists (that is sort of the reason for this operator).
