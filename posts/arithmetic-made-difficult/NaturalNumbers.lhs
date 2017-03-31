---
title: The universal property of the natural numbers
author: nbloomf
date: 2014-05-22
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module NaturalNumbers
>   ( Natural(..), naturalRec, primitiveRec, Nat(), NatShape(..)
>   ) where
> 
> import Nat
> 
> import Test.QuickCheck

We have assumed the existence of a set $\nats$ such that there is a unique inductive set homomorphism from $\nats$ to any other inductive set. But it turns out that this set is not *unique* with this property; any other inductive set which is *isomorphic* to $\nats$ enjoys it as well.

Here's a handwavy proof. Let $(A,\varphi,e)$ be an inductive set, and suppose the unique map $\theta : \nats \rightarrow A$ is bijective. Then there is a unique inductive set homomorphism $\omega : A \rightarrow \nats$; namely, $\omega = \theta^{-1}$. Now any homomorphism from $A$ factors through the (unique) map $\omega$.

From a mathematical point of view, isomorphic objects are interchangeable. But as we'll eventually see, from a *computational* point of view, isomorphic objects can behave very differently. For this reason we will think of the properties of $\nats$ as a kind of interface, and write our programs against that. Specifically, every element of a $\nats$-like set is either the zero or the successor of some other element; we'll represent this with the type ``NatShape``.

> data NatShape t = Zero | Next t

Now every inductive set isomorphic to $\nats$ is characterized by (1) its zero element, (2) its successor function, (3) the unique map $A \rightarrow \nats$, and (4) the unique map $\nats \rightarrow A$. We will also need a helper function to recognize the shape of a natural number, and for convenience a helper to convert a Haskell-native ``Integer`` to a natural number.

> class (Eq t) => Natural t where
>   toNat   :: t -> Nat
>   fromNat :: Nat -> t
> 
>   zero :: t
>   zero = fromNat zero
> 
>   next :: t -> t
>   next = fromNat . next . toNat
> 
>   shapeOf :: t -> NatShape t
>   shapeOf m = case shapeOf $ toNat m of
>     Zero   -> Zero
>     Next k -> Next $ fromNat k
> 
>   natural :: Integer -> t
>   natural = fromNat . mkNat

Here's the ``Natural`` instance for ``Nat``:

> instance Natural Nat where
>   toNat = id
>   fromNat = id
>   zero = Z
>   next = N
> 
>   shapeOf m = case m of
>     Z   -> Zero
>     N k -> Next k
> 
>   natural = mkNat

And note that both natural and primitive recursion can be written against the ``Natural`` interface.

> naturalRec :: (Natural t) => a -> (a -> a) -> t -> a
> naturalRec e phi n =
>   let
>     tau !x k = case shapeOf k of
>       Zero   -> x
>       Next m -> tau (phi x) m
>   in tau e n
> 
> 
> primitiveRec :: (Natural t) =>
>   (a -> b) -> (t -> a -> b -> b) -> t -> a -> b
> primitiveRec phi mu n a =
>   let
>     tau !x h m = case shapeOf m of
>       Zero   -> x
>       Next k -> tau (mu h a x) (next h) k
>   in tau (phi a) zero n

From now on we'll use the ``Natural`` interface with ``naturalRec`` and ``primitiveRec`` instead of ``Nat``.
