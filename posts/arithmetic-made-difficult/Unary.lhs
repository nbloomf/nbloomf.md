---
title: From Arrows to Programs
author: nbloomf
date: 2014-05-07
tags: arithmetic-made-difficult, literate-haskell
slug: unary
---

> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE NoImplicitPrelude #-}
> module Unary
>   ( Unary(Z,N), mkUnary, natRec
>   ) where
> 
> import Prelude (Integer, (-), (<=))
> import Test.QuickCheck.Modifiers (NonNegative(..))
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies

A nice consequence of wrapping up recursion in the $\natrec{\ast}{\ast}$ function is that it allows us to write programs, independent of any implementation, and prove things about them. We'll see lots of examples of this, but first we need to establish some structural results.

<div class="result">
<div class="defn">
Let $1 = \{\ast\}$, and define $\varphi : 1 + \nats \rightarrow 1 + \nats$ by $$\varphi = \rgt \circ \either(\const(\zero),\next).$$ In this post we consider $$(1 + \nats, \lft(\ast), \varphi)$$ as an inductive set.
</div>
</div>

It turns out that $1 + \nats$ is isomorphic to $\nats$, and the map that achieves this is useful.

<div class="result">
<div class="thm">
The natural recursion map $\Theta : \nats \rightarrow 1 + \nats$ is an isomorphism; in particular, the inverse of $\Theta$ is $$\Omega = \either(\const(\zero),\next).$$ We denote this $\Theta$ by $\unnext$.
</div>

<div class="proof"><p>
We need to show two results: first that $\Omega$ is an inductive set homomorphism, and second that $\Omega$ and $\Theta$ are mutual inverses. To the first point, note that
$$\begin{eqnarray*}
 &   & \Omega(\lft(\ast)) \\
 & = & \either(\const(\zero),\id)(\lft(\ast)) \\
 & = & \const(\zero)(\ast) \\
 & = & \zero
\end{eqnarray*}$$
and if $x \in 1 + \nats$, we have two possibilities. If $x = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & \Omega(\varphi(\lft(\ast))) \\
 & = & \Omega((\rgt \circ \either(\const(\zero),\next))(\lft(\ast))) \\
 & = & \Omega(\rgt(\either(\const(\zero),\next)(\lft(\ast)))) \\
 & = & \Omega(\rgt(\const(\zero)(\ast))) \\
 & = & \Omega(\rgt(\zero)) \\
 & = & \either(\const(\zero),\next)(\rgt(\zero)) \\
 & = & \next(\zero) \\
 & = & \next(\Omega(\lft(\ast)))
\end{eqnarray*}$$
and if $x = \rgt(n)$, with $n \in \nats$, we have
$$\begin{eqnarray*}
 &   & \Omega(\varphi(\rgt(n))) \\
 & = & \Omega((\rgt \circ \either(\const(\zero),\next))(\rgt(n))) \\
 & = & \Omega(\rgt(\either(\const(\zero),\next)(\rgt(n)))) \\
 & = & \Omega(\rgt(\next(n))) \\
 & = & \either(\const(\zero),\next)(\rgt(\next(n))) \\
 & = & \next(\next(n)) \\
 & = & \next(\either(\const(\zero),\next)(\rgt(n))) \\
 & = & \next(\Omega(\rgt(n)))
\end{eqnarray*}$$
as needed.

Next to see that $\Omega$ and $\Theta$ are mutual inverses. First we show that $(\Omega \circ \Theta)(n) = \id(n)$ for all $n \in \nats$, proceeding by induction. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & (\Omega \circ \Theta)(n) \\
 & = & \Omega(\Theta(\zero)) \\
 & = & \either(\const(\zero),\next)(\natrec{\lft(\ast)}{\varphi}(\zero)) \\
 & = & \either(\const(\zero),\next)(\lft(\ast)) \\
 & = & \const(\zero)(\ast) \\
 & = & \zero \\
 & = & n,
\end{eqnarray*}$$
and if the equality holds for $n$, we have
$$\begin{eqnarray*}
 &   & (\Omega \circ \Theta)(\next(n)) \\
 & = & \Omega(\Theta(\next(n))) \\
 & = & \either(\const(\zero),\next)(\natrec{\lft(\ast)}{\varphi}(\next(n))) \\
 & = & \either(\const(\zero),\next)(\varphi(\natrec{\lft(\ast)}{\varphi}(n))) \\
 & = & \either(\const(\zero),\next)(\varphi(\Theta(n))) \\
 & = & \either(\const(\zero),\next)((\rgt \circ \either(\const(\zero),\next))(\Theta(n))) \\
 & = & \either(\const(\zero),\next)(\rgt(\either(\const(\zero),\next)(\Theta(n)))) \\
 & = & \next(\either(\const(\zero),\next)(\Theta(n))) \\
 & = & \next(\Omega(\Theta(n))) \\
 & = & \next((\Omega \circ \Theta)(n)) \\
 & = & \next(n)
\end{eqnarray*}$$
as needed. Now to see that $\Theta \circ \Omega = \id$, we consider two possibilities. First note that
$$\begin{eqnarray*}
 &   & (\Theta \circ \Omega)(\lft(\ast)) \\
 & = & \Theta(\Omega(\lft(\ast))) \\
 & = & \Theta(\either(\const(\zero),\next)(\lft(\ast))) \\
 & = & \Theta(\const(\zero)(\ast)) \\
 & = & \Theta(\zero) \\
 & = & \lft(\ast).
\end{eqnarray*}$$
To see that $(\Theta \circ \Omega)(\rgt(n)) = \rgt(n)$ for all $n \in \nats$, we proceed by induction. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & (\Theta \circ \Omega)(\rgt(n)) \\
 & = & \Theta(\Omega(\rgt(\zero))) \\
 & = & \Theta(\either(\const(\zero),\next)(\rgt(\zero))) \\
 & = & \Theta(\next(\zero)) \\
 & = & \natrec{\lft(\ast)}{\varphi}(\next(\zero)) \\
 & = & \varphi(\natrec{\lft(\ast)}{\varphi}(\zero)) \\
 & = & \varphi(\lft(\ast)) \\
 & = & (\rgt \circ \either(\const(\zero),\next))(\lft(\ast)) \\
 & = & \rgt(\either(\const(\zero),\next)(\lft(\ast))) \\
 & = & \rgt(\const(\zero)(\ast)) \\
 & = & \rgt(\zero) \\
 & = & \rgt(n)
\end{eqnarray*}$$
as needed. For the inductive step, if the equality holds for some $n$, we have
$$\begin{eqnarray*}
 &   & (\Theta \circ \Omega)(\rgt(\next(n))) \\
 & = & \Theta(\Omega(\rgt(\next(n)))) \\
 & = & \Theta(\either(\const(\zero),\next)(\rgt(\next(n)))) \\
 & = & \Theta(\next(\next(n))) \\
 & = & \natrec{\lft(\ast)}{\varphi}(\next(\next(n))) \\
 & = & \varphi(\natrec{\lft(\ast)}{\varphi}(\next(n))) \\
 & = & \varphi(\Theta(\next(n))) \\
 & = & \varphi(\Theta(\either(\const(\zero),\next)(\rgt(n)))) \\
 & = & \varphi((\Theta \circ \Omega)(\rgt(n))) \\
 & = & \varphi(\rgt(n)) \\
 & = & (\rgt \circ \either(\const(\zero),\next))(\rgt(n)) \\
 & = & \rgt(\either(\const(\zero),\next)(\rgt(n))) \\
 & = & \rgt(\next(n))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

From $\unnext$ we define two helper functions.

<div class="result">
<div class="defn">
We define $\prev : \nats \rightarrow \nats$ by $$\prev = \either(\const(\zero),\id) \circ \unnext$$ and $\iszero : \nats \rightarrow \bool$ by $$\iszero = \either(\const(\btrue),\const(\bfalse)) \circ \unnext.$$
</div>
</div>

Now $\unnext$, $\prev$, and $\iszero$ have some useful properties.

<div class="result">
<div class="thm"><p>
1. $\unnext(\zero) = \lft(\ast)$.
2. $\unnext(\next(n)) = \rgt(n)$.
3. $\prev(\zero) = \zero$.
4. $\prev(\next(n)) = n$.
5. $\iszero(\zero) = \btrue$.
6. $\iszero(\next(n)) = \bfalse$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \unnext(\zero) \\
 & = & \natrec{\lft(\ast)}{\varphi}(\zero) \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as claimed.
2. Letting $\Omega$ be the inverse of $\unnext$, we have
$$\begin{eqnarray*}
 &   & \unnext(\next(n)) \\
 & = & \unnext(\either(\const(\zero),\next)(\rgt(n))) \\
 & = & \unnext(\Omega(\rgt(n))) \\
 & = & (\unnext \circ \Omega)(\rgt(n)) \\
 & = & \rgt(n)
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \prev(\zero) \\
 & = & (\either(\const(\zero),\id) \circ \unnext)(\zero) \\
 & = & \either(\const(\zero),\id)(\unnext(\zero)) \\
 & = & \either(\const(\zero),\id)(\lft(\ast)) \\
 & = & \const(\zero)(\ast) \\
 & = & \zero
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \prev(\next(n)) \\
 & = & (\either(\const(\zero),\id) \circ \unnext)(\next(n)) \\
 & = & \either(\const(\zero),\id)(\unnext(\next(n))) \\
 & = & \either(\const(\zero),\id)(\rgt(n)) \\
 & = & \id(n) \\
 & = & n
\end{eqnarray*}$$
as claimed.
5. We have
$$\begin{eqnarray*}
 &   & \iszero(\zero) \\
 & = & (\either(\const(\btrue),\const(\bfalse)) \circ \unnext)(\zero) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\unnext(\zero)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\lft(\ast)) \\
 & = & \const(\btrue)(\ast) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
6. We have
$$\begin{eqnarray*}
 &   & \iszero(\next(n)) \\
 & = & (\either(\const(\btrue),\const(\bfalse)) \circ \unnext)(\next(n)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\unnext(\next(n))) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\rgt(n)) \\
 & = & \const(\bfalse)(n) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We're now ready to finish off the Peano axioms.

<div class="result">
<div class="thm"><p>
1. Every natural number is either $\zero$ or of the form $\next(m)$ for some natural number $m$,
2. No natural number is both $\zero$ and $\next(m)$ for some $m$, and
3. $\next(n) = \next(m)$ if and only if $n = m$.
</p></div>

<div class="proof"><p>
1. Let $n \in \nats$ and let $\Omega$ be the inverse of $\unnext$. Consider $\unnext(n) \in 1 + \nats$; we have either $\unnext(n) = \lft(\ast)$ or $\unnext(n) = \rgt(m)$ for some $m \in \nats$. In the first case we have
$$\begin{eqnarray*}
 &   & n \\
 & = & \Omega(\unnext(n)) \\
 & = & \Omega(\lft(\ast)) \\
 & = & \const(\zero)(\ast) \\
 & = & \zero,
\end{eqnarray*}$$
and in the second case we have
$$\begin{eqnarray*}
 &   & n \\
 & = & \Omega(\unnext(n)) \\
 & = & \Omega(\rgt(m)) \\
 & = & \next(m)
\end{eqnarray*}$$
as claimed.
2. If $\zero = \next(n)$, we have $$\btrue = \iszero(\zero) = \iszero(\next(n)) = \bfalse,$$ which is absurd.
3. The "if" part is trivial. To see the "only if" part, suppose we have $\next(n) = \next(m)$; then $$n = \prev(\next(n)) = \prev(\next(m)) = m$$ as claimed.
</p></div>
</div>

Establishing that every natural number is either $\zero$ or of the form $\next(m)$ for some $m$ also justifies our use of the following Haskell type to model the natural numbers.

> data Unary
>   = Z | N Unary
> 
> instance Show Unary where
>   show  Z    = "O"
>   show (N k) = 'I' : show k
> 
> instance TypeName Unary where
>   typeName _ = "Unary"
> 
> instance Equal Unary where
>   eq Z     Z     = True
>   eq Z     (N _) = False
>   eq (N _) Z     = False
>   eq (N x) (N y) = eq x y

(That ``show`` instance is so we can display elements of ``Nat`` without too many parentheses.) We also define a helper function to convert integers into ``Nat``s as follows.

> mkUnary :: Integer -> Unary
> mkUnary k = if k <= 0
>   then Z
>   else N (mkUnary (k-1))

So calling ``mkUnary 7`` in ``ghci``, for instance, prints

    NNNNNNNZ

And we can also give a straightforward implementation of $\natrec{\ast}{\ast}$.

> natRec' :: a -> (a -> a) -> Unary -> a
> natRec' e _    Z    = e
> natRec' e phi (N n) = phi (natRec' e phi n)

For example:

    let theta' = natRec' True not

and we can test out this map by evaluating it on several natural numbers:

    > theta' $ mkUnary 10
    True
    > theta' $ mkUnary 11
    False

Now this ``theta'`` is pretty silly (though not *that* silly, it detects the parity of a natural number, which we haven't defined yet). But in the next section we'll define a more interesting recursive function.


But...
------

There is a practical problem with this implementation of ``natRec'``. If we evaluate on a natural number like ``NNNZ``, the "stack" of function calls expands to something like this:

       natRec' e phi (N $ N $ N Z)
    == phi $ natRec' e phi (N $ N Z)
    == phi $ phi $ natRec' e phi (N Z)
    == phi $ phi $ phi $ natRec' e phi Z
    == phi $ phi $ phi $ e
    == phi $ phi $ e'
    == phi $ e''
    == e'''

So we generate a tower of unevaluated calls to ``phi``, $n$ tall, before collapsing it down again. In the meantime all those unevaluated ``phi``s are sitting in memory. It is not difficult to see that if we evaluate ``natRec'`` on a "larger" number (whatever that means) we will quickly run out of actual memory. To help with this, we can try rewriting ``natRec`` in so-called "tail call" recursive form like so.

> natRec :: a -> (a -> a) -> Unary -> a
> natRec e phi n =
>   let
>     tau !x k = case k of
>       Z   -> x
>       N m -> tau (phi x) m
>   in tau e n

Now ``natRec`` does not leave a bunch of unevaluated functions in memory. It is effectively a loop, iterating "up" from 0 (again with the scare quotes because we don't have an order on $\nats$ yet but of course you know what it means) rather than "down" from $n$. So this version expands to something like this:

       natRec e phi (N $ N $ N Z)
    == tau e (N $ N $ N Z)
    == tau e' (N $ N Z)
    == tau e'' (N Z)
    == tau e''' Z
    == e'''

It deconstructs its natural number argument and evaluates ``phi`` strictly at each step. (That is what the bang pattern and ``$!`` are for.) At least I think that's what it does; my simple testing shows that ``natRec'`` easily falls down while ``natRec`` does not. But profiling Haskell seems like a bit of dark art to me still. I am open to being wrong here.

We can see that ``natRec`` has better performance than ``natRec'``, but there is a hitch. ``natRec'`` is obviously an implementation of $\natrec{\ast}{\ast}$. But it is **not** obvious that ``natRec`` and ``natRec'`` are the same function! This is where the universal property of natural recursion comes in: if we can show that both functions satisfy the universal property, then *they must be the same*. And we can do this using induction.

First, we claim that for all ``n :: Nat``,

    natRec' (phi e) phi n == phi $ natRec' e phi n

Using induction, it suffices to note that

       natRec' (phi e) phi Z
    == phi e
    == phi $ natRec' e phi Z

and that if the equation holds for ``n``, then

       natRec' (phi e) phi (N n)
    == phi $ natRec' (phi e) phi n
    == phi $ phi $ natRec' e phi n
    == phi $ natRec' e phi (N n)

Now, again using induction, we have

       natRec e phi Z
    == tau e Z
    == e
    == natRec' e phi Z

and if ``natRec e phi n == natRec' e phi n``, then

       natRec e phi (N n)
    == tau e (N n)
    == tau (phi e) n
    == natRec (phi e) phi n
    == natRec' (phi e) phi n
    == phi $ natRec' e phi n
    == natRec' e phi (N n)

Since ``natRec e phi`` and ``natRec' e phi`` are both functions with signature ``Unary -> a`` which satisfy the universal property of $\nats$, they must be the same function: equal on all inputs.

This is a powerful idea. We've effectively written a slow but obviously correct program, and then proven it is equivalent to a more efficient one. We'll be doing more of this later.


Testing
-------

Along the way we'll be writing some proofs involving ``Nat``s, but it is also useful to do some automated testing. I'll toss in an ``Arbitrary`` instance here.

> instance Arbitrary Unary where
>   arbitrary = do
>     NonNegative k <- arbitrary
>     return (mkUnary k)
>
>   shrink  Z    = []
>   shrink (N k) = [k]
> 
> instance CoArbitrary Unary where
>   coarbitrary Z = variant 0
>   coarbitrary (N x) = variant 1 . coarbitrary x

We can try out this instance with the following command.

```haskell
$> generate (arbitrary :: Gen Unary)
```
