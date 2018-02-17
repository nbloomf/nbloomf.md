---
title: From Arrows to Programs
author: nbloomf
date: 2014-05-07
tags: arithmetic-made-difficult, literate-haskell
slug: unary
---

> {-# LANGUAGE NoImplicitPrelude, BangPatterns #-}
> module Unary
>   ( Unary(Z,N), mkUnary, natRec, natRec'
>   ) where
> 
> import Prelude (Integer, (-), (<=))
> import Test.QuickCheck.Modifiers (NonNegative(..))
> import Testing
> import Booleans

A nice consequence of wrapping up recursion in the $\natrec$ function is that it allows us to write programs, independent of any implementation, and prove things about them. We'll see lots of examples of this, but first we need to establish some structural results.

:::::: definition ::
[]{#def-unnext}
Let $1 = \{\ast\}$, and define $\varphi : 1 + \nats \rightarrow 1 + \nats$ by $$\varphi = \compose(\rgt)(\either(\const(\zero),\id)).$$ In this post we consider $$(1 + \nats, \lft(\ast), \varphi)$$ as an inductive set, and denote the natural recursion map $\nats \rightarrow 1 + \nats$ by $\unnext$.
::::::::::::::::::::

We can evaluate $\unnext$ directly.

:::::: theorem :::::
[]{#thm-unnext-zero}[]{#thm-unnext-next}
If $n \in \nats$, we have the following.

1. $\unnext(\zero) = \lft(\ast)$.
2. $\unnext(\next(n)) = \rgt(n)$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \unnext(\zero) \\
 &     \href{@unary@#def-unnext}
   = & \natrec(\lft(\ast))(\compose(\rgt)(\either(\const(\zero),\next)))(\zero) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \lft(\ast)
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $n$. For the base case $n = \zero$, note that
$$\begin{eqnarray*}
 &   & \unnext(\next(\zero)) \\
 &     \href{@unary@#def-unnext}
   = & \natrec(\lft(\ast))(\compose(\rgt)(\either(\const(\zero),\next)))(\next(\zero)) \\
 &     \href{@peano@#cor-natrec-next}
   = & \compose(\rgt)(\either(\const(\zero),\next))(\natrec(\lft(\ast))(\compose(\rgt)(\either(\const(\zero),\next)))(\zero)) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \compose(\rgt)(\either(\const(\zero),\next))(\lft(\ast)) \\
 &     \href{@functions@#def-compose}
   = & \rgt(\either(\const(\zero),\next)(\lft(\ast))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \rgt(\const(\zero)(\ast)) \\
 &     \href{@functions@#def-const}
   = & \rgt(\zero)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now we have
$$\begin{eqnarray*}
 &   & \unnext(\next(\next(n))) \\
 &     \href{@unary@#def-unnext}
   = & \natrec(\lft(\ast))(\compose(\rgt)(\either(\const(\zero),\next)))(\next(\next(n))) \\
 &     \href{@peano@#cor-natrec-next}
   = & \compose(\rgt)(\either(\const(\zero),\next))(\natrec(\lft(\ast))(\compose(\rgt)(\either(\const(\zero),\next)))(\next(n))) \\
 &     \href{@unary@#def-unnext}
   = & \compose(\rgt)(\either(\const(\zero),\next))(\unnext(\next(n))) \\
 &     \hyp{\unnext(\next(n)) = \rgt(n)}
   = & \compose(\rgt)(\either(\const(\zero),\next))(\rgt(n)) \\
 &     \href{@functions@#def-compose}
   = & \rgt(\either(\const(\zero),\next)(\rgt(n))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \rgt(\next(n))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

It turns out that $1 + \nats$ is isomorphic to $\nats$, and the map that achieves this is useful.

:::::: theorem :::::
[]{#thm-unnext-inverse}
The map $\unnext : \nats \rightarrow 1 + \nats$ is an isomorphism; in particular, the inverse of $\unnext$ is $$Ω = \either(\const(\zero),\next).$$

::: proof ::::::::::
We need to show two results: first that $Ω$ is an inductive set homomorphism, and second that $Ω$ and $\Theta$ are mutual inverses. To the first point, note that
$$\begin{eqnarray*}
 &   & Ω(\lft(\ast)) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \either(\const(\zero),\next)(\lft(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\zero)(\ast) \\
 &     \href{@functions@#def-const}
   = & \zero
\end{eqnarray*}$$
and if $x \in 1 + \nats$, we have two possibilities. If $x = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & Ω(\compose(\rgt)(\either(\const(\zero),\next))(\lft(\ast))) \\
 &     \href{@functions@#def-compose}
   = & Ω(\rgt(\either(\const(\zero),\next)(\lft(\ast)))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & Ω(\rgt(\const(\zero)(\ast))) \\
 &     \href{@functions@#def-const}
   = & Ω(\rgt(\zero)) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \either(\const(\zero),\next)(\rgt(\zero)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \next(\zero) \\
 &     \href{@functions@#def-const}
   = & \next(\const(\zero)(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \next(\either(\const(\zero),\next)(\lft(\ast))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \next(Ω(\lft(\ast)))
\end{eqnarray*}$$
and if $x = \rgt(n)$, with $n \in \nats$, we have
$$\begin{eqnarray*}
 &   & Ω(\compose(\rgt)(\either(\const(\zero),\next))(\rgt(n))) \\
 &     \href{@functions@#def-compose}
   = & Ω(\rgt(\either(\const(\zero),\next)(\rgt(n)))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & Ω(\rgt(\next(n))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \either(\const(\zero),\next)(\rgt(\next(n))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \next(\next(n)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \next(\either(\const(\zero),\next)(\rgt(n))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \next(Ω(\rgt(n)))
\end{eqnarray*}$$
as needed.

Next to see that $Ω$ and $\Theta$ are mutual inverses. First we show that $\compose(Ω)(\unnext)(n) = \id(n)$ for all $n \in \nats$, proceeding by induction. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \compose(Ω)(\unnext)(\zero) \\
 &     \href{@functions@#def-compose}
   = & Ω(\unnext(\zero)) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \either(\const(\zero),\next)(\unnext(\zero)) \\
 &     \href{@unary@#thm-unnext-zero}
   = & \either(\const(\zero),\next)(\lft(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\zero)(\ast) \\
 &     \href{@functions@#def-const}
   = & \zero
\end{eqnarray*}$$
and if the equality holds for $n$, we have
$$\begin{eqnarray*}
 &   & \compose(Ω)(\unnext)(\next(n)) \\
 &     \href{@functions@#def-compose}
   = & Ω(\unnext(\next(n))) \\
 &     \href{@unary@#thm-unnext-next}
   = & Ω(\rgt(n)) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \either(\const(\zero),\next)(\rgt(n)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \next(n)
\end{eqnarray*}$$
as needed. Now to see that $\Theta \circ Ω = \id$, we consider two possibilities. First note that
$$\begin{eqnarray*}
 &   & \compose(\unnext)(Ω)(\lft(\ast)) \\
 &     \href{@functions@#def-compose}
   = & \unnext(Ω(\lft(\ast))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \unnext(\either(\const(\zero),\next)(\lft(\ast))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \unnext(\const(\zero)(\ast)) \\
 &     \href{@functions@#def-const}
   = & \unnext(\zero) \\
 &     \href{@unary@#thm-unnext-zero}
   = & \lft(\ast)
\end{eqnarray*}$$
To see that $(\Theta \circ Ω)(\rgt(n)) = \rgt(n)$ for all $n \in \nats$, we proceed by induction. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \compose(\unnext)(Ω)(\rgt(\zero)) \\
 &     \href{@functions@#def-compose}
   = & \unnext(Ω(\rgt(\zero))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \unnext(\either(\const(\zero),\next)(\rgt(\zero))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \unnext(\next(\zero)) \\
 &     \href{@unary@#thm-unnext-next}
   = & \rgt(\zero)
\end{eqnarray*}$$
as needed. For the inductive step, if the equality holds for some $n$, we have
$$\begin{eqnarray*}
 &   & \compose(\unnext)(Ω)(\rgt(\next(n))) \\
 &     \href{@functions@#def-compose}
   = & \unnext(Ω(\rgt(\next(n)))) \\
 &     \let{Ω = \either(\const(\zero),\next)}
   = & \unnext(\either(\const(\zero),\next)(\rgt(\next(n)))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \unnext(\next(\next(n))) \\
 &     \href{@unary@#thm-unnext-next}
   = & \rgt(\next(n))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

From $\unnext$ we define two helper functions.

:::::: definition ::
[]{#def-prev}[]{#def-iszero}
We define $\prev : \nats \rightarrow \nats$ by $$\prev = \compose(\either(\const(\zero),\id))(\unnext)$$ and $\iszero : \nats \rightarrow \bool$ by $$\iszero = \compose(\either(\const(\btrue),\const(\bfalse)))(\unnext).$$
::::::::::::::::::::

Now $\prev$, and $\iszero$ have some useful properties.

:::::: theorem :::::
[]{#thm-prev-zero}[]{#thm-prev-next}[]{#thm-iszero-zero}[]{#thm-iszero-next}
1. $\prev(\zero) = \zero$.
2. $\prev(\next(n)) = n$.
3. $\iszero(\zero) = \btrue$.
4. $\iszero(\next(n)) = \bfalse$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \prev(\zero) \\
 &     \href{@unary@#def-prev}
   = & \compose(\either(\const(\zero),\id))(\unnext)(\zero) \\
 &     \href{@functions@#def-compose}
   = & \either(\const(\zero),\id)(\unnext(\zero)) \\
 &     \href{@unary@#thm-unnext-zero}
   = & \either(\const(\zero),\id)(\lft(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\zero)(\ast) \\
 &     \href{@functions@#def-const}
   = & \zero
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \prev(\next(n)) \\
 &     \href{@unary@#def-prev}
   = & \compose(\either(\const(\zero),\id))(\unnext)(\next(n)) \\
 &     \href{@functions@#def-compose}
   = & \either(\const(\zero),\id)(\unnext(\next(n))) \\
 &     \href{@unary@#thm-unnext-next}
   = & \either(\const(\zero),\id)(\rgt(n)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \id(n) \\
 &     \href{@functions@#def-id}
   = & n
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \iszero(\zero) \\
 &     \href{@unary@#def-iszero}
   = & \compose(\either(\const(\btrue),\const(\bfalse)))(\unnext)(\zero) \\
 &     \href{@functions@#def-compose}
   = & \either(\const(\btrue),\const(\bfalse))(\unnext(\zero)) \\
 &     \href{@unary@#thm-unnext-zero}
   = & \either(\const(\btrue),\const(\bfalse))(\lft(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\btrue)(\ast) \\
 &     \href{@functions@#def-const}
   = & \btrue
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \iszero(\next(n)) \\
 &     \href{@unary@#def-iszero}
   = & \compose(\either(\const(\btrue),\const(\bfalse)))(\unnext)(\next(n)) \\
 &     \href{@functions@#def-compose}
   = & \either(\const(\btrue),\const(\bfalse))(\unnext(\next(n))) \\
 &     \href{@unary@#thm-unnext-next}
   = & \either(\const(\btrue),\const(\bfalse))(\rgt(n)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \const(\bfalse)(n) \\
 &     \href{@functions@#def-const}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::

We're now ready to finish off the Peano axioms.

:::::: theorem :::::
1. Every natural number is either $\zero$ or of the form $\next(m)$ for some natural number $m$,
2. No natural number is both $\zero$ and $\next(m)$ for some $m$, and
3. $\next(n) = \next(m)$ if and only if $n = m$.

::: proof ::::::::::
1. Let $n \in \nats$. Consider $\unnext(n) \in 1 + \nats$; we have either $\unnext(n) = \lft(\ast)$ or $\unnext(n) = \rgt(m)$ for some $m \in \nats$. In the first case we have
$$\begin{eqnarray*}
 &   & n \\
 &     \href{@functions@#def-id}
   = & \id(n) \\
 &     \href{@unary@#thm-unnext-inverse-left}
   = & \compose(\either(\const(\zero),\next))(\unnext)(n) \\
 &     \href{@functions@#def-compose}
   = & \either(\const(\zero),\next)(\unnext(n)) \\
 &     \hyp{\unnext(n) = \lft(\ast)}
   = & \either(\const(\zero),\next)(\lft(\ast)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\zero)(\ast) \\
 &     \href{@functions@#def-const}
   = & \zero
\end{eqnarray*}$$
and in the second case we have
$$\begin{eqnarray*}
 &   & n \\
 &     \href{@functions@#def-id}
   = & \id(n) \\
 &     \compose(\either(\const(\zero),\next))(\unnext)(n) \\
   = & \either(\const(\zero),\next)(\unnext(n)) \\
 &     \hyp{\unnext(n) = \rgt(m)}
   = & \either(\const(\zero),\next)(\rgt(m)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \next(m)
\end{eqnarray*}$$
as claimed.
2. If $\zero = \next(n)$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 &     \href{@unary@#thm-iszero-zero}
   = & \iszero(\zero) \\
 &     \hyp{\next(n) = \zero}
   = & \iszero(\next(n)) \\
 &     \href{@unary@#thm-iszero-next}
   = & \bfalse
\end{eqnarray*}$$
which is absurd.
3. The "if" part is trivial. To see the "only if" part, suppose we have $\next(n) = \next(m)$; then
$$\begin{eqnarray*}
 &   & n \\
 &     \href{@unary@#thm-prev-next}
   = & \prev(\next(n)) \\
 &     \hyp{\next(n) = \next(m)}
   = & \prev(\next(m)) \\
 &     \href{@unary@#thm-prev-next}
   = & m
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::

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
>   eq Z     Z     = true
>   eq Z     (N _) = false
>   eq (N _) Z     = false
>   eq (N x) (N y) = eq x y

(That ``show`` instance is so we can display elements of ``Nat`` without too many parentheses.) We also define a helper function to convert integers into ``Nat``s as follows.

> mkUnary :: Integer -> Unary
> mkUnary k = if k <= 0
>   then Z
>   else N (mkUnary (k-1))

So calling ``mkUnary 7`` in ``ghci``, for instance, prints

    NNNNNNNZ

And we can also give a straightforward implementation of $\natrec(\ast)(\ast)$.

> natRec' :: a -> (a -> a) -> Unary -> a
> natRec' e _    Z    = e
> natRec' e phi (N n) = phi (natRec' e phi n)

For example:

    let theta' = natRec' true not

and we can test out this map by evaluating it on several natural numbers:

    > theta' $ mkUnary 10
    true
    > theta' $ mkUnary 11
    false

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

We can see that ``natRec`` has better performance than ``natRec'``, but there is a hitch. ``natRec'`` is obviously an implementation of $\natrec(\ast)(\ast)$. But it is **not** obvious that ``natRec`` and ``natRec'`` are the same function! This is where the universal property of natural recursion comes in: if we can show that both functions satisfy the universal property, then *they must be the same*. And we can do this using induction.

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
>   coarbitrary Z = variant (0 :: Integer)
>   coarbitrary (N x) = variant (1 :: Integer) . coarbitrary x

We can try out this instance with the following command.

```haskell
$> generate (arbitrary :: Gen Unary)
```
