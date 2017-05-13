---
title: The Uniqueness of the Natural Numbers
author: nbloomf
date: 2014-05-22
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module NaturalNumbers
>   ( Natural(..), NatShape(..), Nat(..), Unary()
>   , isZero, prev, naturalRec, simpleRec, bailoutRec
>   , _test_nat, main_nat
>   ) where
> 
> import Booleans
> 
> import Unary
> 
> import Prelude(Show(..), IO, Bool(..), Integer, Int, return, sequence_, (.))
> import Test.QuickCheck

We have assumed the existence of a set $\nats$ such that there is a unique inductive set homomorphism from $\nats$ to any other inductive set. But it turns out that this set is not *unique* with this property; any other inductive set which is *isomorphic* to $\nats$ enjoys it as well.

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

And some helpers:

> isZero :: (Natural n) => n -> Bool
> isZero m = case natShape m of
>   Zero   -> True
>   Next _ -> False
> 
> prev :: (Natural n) => n -> n
> prev m = case natShape m of
>   Zero   -> zero
>   Next k -> k

Here's the ``Natural`` instance for ``Unary``:

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

And note that natural, simple, and primitive recursion can be written against the ``Natural`` interface.

> naturalRec :: (Natural n)
>   => a
>   -> (a -> a)
>   -> n
>   -> a
> naturalRec e phi n =
>   let
>     tau !x k = case natShape k of
>       Zero   -> x
>       Next m -> tau (phi x) m
>   in tau e n
> 
> 
> simpleRec :: (Natural n)
>   => (a -> b)
>   -> (n -> a -> b -> b)
>   -> n
>   -> a
>   -> b
> simpleRec phi mu n a =
>   let
>     tau !x h m = case natShape m of
>       Zero   -> x
>       Next k -> tau (mu h a x) (next h) k
>   in tau (phi a) zero n
> 
> 
> bailoutRec :: (Natural n)
>   => (a -> b)
>   -> (n -> a -> Bool)
>   -> (n -> a -> b)
>   -> (n -> a -> a)
>   -> n
>   -> a
>   -> b
> bailoutRec phi beta psi omega =
>   let
>     theta n a = case natShape n of
>       Zero -> phi a
>
>       Next m ->
>         if beta m a
>           then psi m a
>           else theta m (omega m a)
> 
>   in theta

From now on we'll use the ``Natural`` interface with ``naturalRec`` and ``simpleRec`` instead of ``Unary``.

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


Equality
--------

We have an implicit equality among natural numbers, but in this post we'll make that relation computable. We won't say much else about this function.

<div class="result">
<div class="thm"><p>
Define $\beta : \nats \times \nats \rightarrow \bool$ by $$\beta(a,b) = \iszero(b),$$ $\psi : \nats \times \nats \rightarrow \bool$ by $$\psi(a,b) = \bfalse,$$ and $\omega : \nats \times \nats \rightarrow \nats$ by $$\omega(a,b) = \prev(b).$$ Now define $\nequal : \nats \times \nats \rightarrow \bool$ by $$\nequal = \bailrec{\iszero}{\beta}{\psi}{\omega}.$$

Then $$\nequal(a,b) = \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ a = b \\ \bfalse & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case, $a = \zero$, note that
$$\begin{eqnarray*}
 &   & \nequal(a,b) \\
 & = & \iszero(b) \\
 & = & \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ b = a \\ \bfalse & \mathrm{otherwise} \end{array} \right.
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the result holds for some $a$. Now if $b = \zero$, we have $\nequal(\next(a),b) = \bfalse$, and indeed $\zero \neq \next(a)$. If $b \neq \zero$, then we have 
$$\begin{eqnarray*}
 &   & \nequal(\next(a),b) \\
 & = & \nequal(a,\prev(b)).
\end{eqnarray*}$$
And indeed, we have $$\next(a) = b$$ if and only if $$\prev(\next(a)) = \prev(b)$$ if and only if $$a = \prev(b)$$ as claimed.
</p></div>
</div>

In Haskell:

> instance (Natural t) => Equal (Nat t) where
>   eq = bailoutRec isZero beta psi omega
>     where
>       beta  _ b = isZero b
>       psi   _ _ = False
>       omega _ b = prev b

Note that we'll be writing functions against ``Nat t``, which is isomorphic to ``t``. This is so we can avoid undecidable instance declarations in Haskell.


Testing
-------

Let's give ``Natural`` a test drive. :) Here's a test of one simple property of equality.

> -- eq(a,a) == True
> _test_eq_reflexive :: (Natural n) => n -> Nat n -> Bool
> _test_eq_reflexive _ a =
>   (eq a a) ==== True

And a test wrapper:

> -- run all tests for eq
> _test_nat :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_nat t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_eq_reflexive t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And a default main function:

> main_nat :: IO ()
> main_nat = _test_nat (zero :: Unary) 20 100
