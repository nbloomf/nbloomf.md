---
title: The Uniqueness of the Natural Numbers
author: nbloomf
date: 2014-05-23
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module NaturalNumbers
>   ( Natural(..), NatShape(..), Nat(..), Unary()
>   , isZero, prev, naturalRec
>   ) where
> 
> import Booleans
> import Unary
> 
> import Prelude(Show(..), IO, Bool(..),
>   Integer, Int, return, sequence_, (.))
> import Test.QuickCheck

We have assumed the existence of a set $\nats$ such that there is a unique inductive set homomorphism from $\nats$ to any other inductive set. But it turns out that this set is not *unique* with this property; any other inductive set which is *isomorphic* to $\nats$ enjoys it as well. In fact we've already seen one such set, namely $1 + \nats$.

Here's a handwavy proof. Let $(A,\varphi,e)$ be an inductive set, and suppose the unique map $\theta : \nats \rightarrow A$ is bijective. Then there is a unique inductive set homomorphism $\omega : A \rightarrow \nats$; namely, $\omega = \theta^{-1}$. Now any homomorphism from $A$ factors through the (unique) map $\omega$.

From a mathematical point of view, isomorphic objects are interchangeable. But as we'll eventually see, from a *computational* point of view, isomorphic objects can behave very differently. For this reason we will think of the properties of $\nats$ as a kind of interface, and write our programs against that. Specifically, every element of a $\nats$-like set is either the zero or the successor of some other element; we'll represent this with the type ``NatShape``.

> data NatShape n = Zero | Next n

Now every inductive set isomorphic to $\nats$ is characterized by (1) its zero element, (2) its successor function, (3) the unique map $A \rightarrow \nats$, and (4) the unique map $\nats \rightarrow A$. We will also need a helper function to recognize the shape of a natural number, and for convenience a helper to convert a Haskell-native ``Integer`` to a natural number.

> class Natural n where
>   toUnary   :: n -> Unary
>   fromUnary :: Unary -> n
> 
>   zero :: n
>   zero = fromUnary zero
> 
>   next :: n -> n
>   next = fromUnary . next . toUnary
> 
>   natural :: Integer -> n
>   natural = fromUnary . mkUnary
> 
>   natShape :: n -> NatShape n
>   natShape m = case natShape (toUnary m) of
>     Zero   -> Zero
>     Next k -> Next (fromUnary k)

Our helpers $\iszero$ and $\prev$ can be written against this interface:

> isZero :: (Natural n) => n -> Bool
> isZero m = case natShape m of
>   Zero   -> True
>   Next _ -> False
> 
> prev :: (Natural n) => n -> n
> prev m = case natShape m of
>   Zero   -> zero
>   Next k -> k

As can the natural recursion operator $\natrec{\ast}{\ast}$.

> naturalRec :: (Natural n)
>   => a -> (a -> a) -> n -> a
> naturalRec e phi n =
>   let
>     tau !x k = case natShape k of
>       Zero   -> x
>       Next m -> tau (phi x) m
>   in tau e n

From now on we'll write programs against the ``Natural`` interface with ``naturalRec`` instead of ``Unary`` specifically. Of course, ``Unary`` is an instance of ``Natural``:

> instance Natural Unary where
>   toUnary   x = x
>   fromUnary x = x
> 
>   zero = Z
>   next = N
> 
>   natShape m = case m of
>     Z   -> Zero
>     N k -> Next k
> 
>   natural = mkUnary

There is one bit of Haskell wierdness we have to deal with. We can define an ``Equal`` instance against the ``Natural`` interface (as we'll see), but the instance declaration

```haskell
instance (Natural t) => Equal t where
  ...
```

is undecidable. To get around this we'll use a wrapper type, ``Nat``.

> newtype Nat n = Nat { unNat :: n }
> 
> 
> instance (Show t) => Show (Nat t) where
>   show = show . unNat
> 
> 
> instance (Natural t) => Natural (Nat t) where
>   toUnary   = toUnary . unNat
>   fromUnary = Nat . fromUnary
> 
>   zero = Nat zero
> 
>   next = Nat . next . unNat
> 
>   natural = Nat . natural
> 
>   natShape (Nat x) = case natShape x of
>     Zero   -> Zero
>     Next y -> Next (Nat y)
> 
> 
> instance (Arbitrary a) => Arbitrary (Nat a) where
>   arbitrary = do
>     x <- arbitrary
>     return (Nat x)

Okay!

