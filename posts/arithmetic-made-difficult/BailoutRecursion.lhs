---
title: Bailout Recursion
author: nbloomf
date: 2014-05-21
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module BailoutRecursion
>   ( bailRec
>   ) where
> 
> import Nat

So far we have defined two special *recursion operators*, $\natrec{\ast}{\ast}$ and $\simprec{\ast}{\ast}$. These act like program skeletons: fill in the slots with functions of the right signatures and get a computable function out. In this post we'll define one more operator, which we will call *bailout recursion*.

<div class="result">
<div class="thm">
Suppose we have sets $A$ and $B$ and functions with the following signatures:
$$\begin{eqnarray*}
\varphi & : & A \rightarrow B \\
\beta & : & \nats \times A \rightarrow \bool \\
\psi & : & \nats \times A \rightarrow B \\
\omega & : & \nats \times A \rightarrow A. \\
\end{eqnarray*}$$

Then there is a unique function $\Theta : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$\Theta(\zero, a) = \varphi(a)$$ and $$\Theta(\next(m), a) = \left\{ \begin{array}{ll} \psi(m,a) & \mathrm{if}\ \beta(m,a) \\ \Theta(m, \omega(m,a)) & \mathrm{otherwise}. \end{array}\right.$$

This function $\Theta$ will be denoted $\bailrec{\varphi}{\beta}{\psi}{\omega}$.
</div>

<div class="proof">
This proof will be very similar to the analogous proof for simple recursion.

First we establish existence. To this end, define a map $W : \nats \times {}^AB \rightarrow {}^AB$ by $$W(m,h)(x) = \left\{ \begin{array}{ll} \psi(m,x) & \mathrm{if}\ \beta(m,x) \\ h(\omega(m,x)) & \mathrm{otherwise}, \end{array} \right.$$ and define $t : \nats \times {}^AB \rightarrow \nats \times {}^AB$ by $$t(m,h) = (\next(m), W(m,h)).$$

Now we define $\Theta$ as follows: $$\Theta(m,a) = \snd((\natrec{(\zero, \varphi)}{t})(m))(a).$$

($\snd$ is the map which selects the second entry of a pair.)

Note that
$$\begin{eqnarray*}
 &   & \Theta(\zero,a) \\
 & = & (\snd(\natrec{(\zero, \varphi)}{t})(\zero))(a) \\
 & = & (\snd(\zero, \varphi))(a) \\
 & = & \varphi(a).
\end{eqnarray*}$$

To show the second property of $\Theta$, we will show by induction that the following (compound) statement holds for all $n \in \nats$:

1. $\natrec{(\zero,\varphi)}{t}(n) = (n, \lambda x: \Theta(n,x))$ and
2. $\Theta(\next(n), a) = W(n,\lambda x: \Theta(n,x))(a)$ for all $a \in A$.

For the base case, note that

$$\begin{eqnarray*}
 &   & \natrec{(\zero, \varphi)}{t}(\zero) \\
 & = & (\zero, \varphi) \\
 & = & (\zero, \lambda x : \varphi(x)) \\
 & = & (\zero, \lambda x : \Theta(\zero, x))
\end{eqnarray*}$$

and that for all $a \in A$,

$$\begin{eqnarray*}
 &   & \Theta(\next\ \zero, a) \\
 & = & (\snd (\natrec{(\zero, \varphi)}{t}(\next\ \zero)))(a) \\
 & = & (\snd (t(\natrec{(\zero, \varphi)}{t}(\zero))))(a) \\
 & = & (\snd (t(\zero, \varphi)))(a) \\
 & = & (\snd (\next\ \zero, W(\zero, \varphi)))(a). \\
 & = & W(\zero, \varphi)(a). \\
 & = & W(\zero, \lambda x: \varphi(x))(a). \\
 & = & W(\zero, \lambda x: \Theta(\zero,x))(a). \\
\end{eqnarray*}$$

Now for the inductive step, suppose the statement holds for $n \in \nats$. Then we have

$$\begin{eqnarray*}
 &   & \natrec{(\zero, \varphi)}{t}(\next\ n) \\
 & = & t(\natrec{(\zero, \varphi)}{t}(n)) \\
 & = & t(n, \lambda x : \Theta(n,x)) \\
 & = & (\next\ n, W(n, \lambda x : \Theta(n,x))) \\
 & = & (\next\ n, \lambda y : W(n, \lambda x : \Theta(n,x))(y)) \\
 & = & (\next\ n, \lambda y : \Theta(\next\ n, y)
\end{eqnarray*}$$

(Note that we used both parts of the induction hypothesis here.) Also note that
$$\begin{eqnarray*}
 &   & \Theta(\next(\next\ n), a) \\
 & = & \snd (\natrec{(\zero, \varphi)}{t}(\next(\next\ n)))(a) \\
 & = & \snd (t (\natrec{(\zero, \varphi)}{t}(\next\ n)))(a) \\
 & = & \snd (t (\next\ n, \lambda x : \Theta(\next\ n, x)))(a) \\
 & = & \snd (\next(\next\ n), W(\next\ n, \lambda x : \Theta(\next\ n,x)))(a) \\
 & = & W(\next\ n, \lambda x : \Theta(\next\ n, x))(a).
\end{eqnarray*}$$

So $\Theta$ has the claimed properties by induction. To see that $\Theta$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $\Theta$. Then we have $$\Psi(\zero, a) = \varphi(a) = \Theta(\zero, a)$$ for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = \Theta(n, a)$ for all $a \in A$, we have

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \psi(n,a) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

if $\beta(n,a) = \btrue$, and

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \Psi(n, \omega(n,a)) \\
 & = & \Theta(n, \omega(n,a)) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

if not, for all $a \in A$. Thus $\Psi = \Theta$ as needed.
</div>
</div>

You might notice that in this proof, we didn't really use $\beta$ or $\psi$, and the fact that $W$ is piecewise-defined plays no role. When this happens in a proof it usually means we've got some unnecessary details. But in this case, we will be using $\beta$ and $\psi$ later, and the piecewiseness of $\Theta$ will be crucial in constructing an efficient tail-recursive evaluation strategy. Stay tuned. :)


Implementation
--------------

As we did with $\natrec{\ast}{\ast}$ and $\simprec{\ast}{\ast}$, we'd like to implement $\bailrec{\ast}{\ast}{\ast}{\ast}$ in software. There are a couple of ways to go about this. First, the signature.

> bailRec, bailRec'
>   :: (a -> b)
>   -> (Nat -> a -> Bool)
>   -> (Nat -> a -> b)
>   -> (Nat -> a -> a)
>   -> Nat
>   -> a
>   -> b

There's the naive way:

> bailRec phi beta psi omega =
>   let
>     theta n a = case n of
>       Z -> phi a
>
>       N m ->
>         if beta m a
>           then psi m a
>           else theta m (omega m a)
> 
>   in theta

And there's the definition from the proof:

> bailRec' phi beta psi omega = \n a ->
>   let
>     w m h x =
>       if beta m x
>         then psi m x
>         else h $ omega m x
>  
>     t (m,h) = (N m, w m h)
> 
>   in snd (natRec (Z, phi) t n) $ a

Unlike simple recursion, the naive implementation of bailout recursion is already tail recursive.


What it does
------------

Bailout recursion does some cool things that simple recursion does not. The $\omega$ map lets us "mutate" the initial parameter $a$ at each step in the recursion, and the boolean-valued function $\beta$ lets us short-circuit the recursion.

Also note that simple recursion and bailout recursion were carefully chosen to have *tail recursive* evaluation strategies. Roughly speaking, a recursive function is called *tail recursive* if there is "nothing left to do" after the recursive call. For example, $$f(n+1) = 1 + f(n)$$ is *not* tail recursive, because on the right hand side there is something waiting for the result of the recursive evaluation -- in this case, the $1+$.

Arbitrary recursion is dangerous because in general, every time one function uses another we have to keep track of what remains to be done afterward -- if we aren't careful, it is very easy to write recursive functions which eat up lots of memory. Even simple recursion can blow up exponentially; the classic example is the Fibonacci numbers (which we'll see later).

In contrast, a *tail recursive* function by definition doesn't have to keep track of what remains to be done after the recursion. Our recursion operators, $\natrec{\ast}{\ast}$, $\simprec{\ast}{\ast}$, and $\bailrec{\ast}{\ast}{\ast}{\ast}$, are carefully chosen so that they have tail recursive implementations.

By the way, I think it's helpful to compare the difference between arbitrary recursion and recursion operators to the difference between arbitrary ``GOTO``s and structured loops. In both cases we have a simple but dangerous primitive operation that is hidden behind a safer and more meaningful interface. A ``for`` loop means "repeat this some number of times"; while the meaning of simple recursion is given by its universal property.
