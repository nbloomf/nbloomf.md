---
title: The Uniqueness of the Natural Numbers
author: nbloomf
date: 2014-05-23
tags: arithmetic-made-difficult, literate-haskell
slug: nats
---

> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE NoImplicitPrelude #-}
> module NaturalNumbers
>   ( Natural(..), Unary()
>   , isZero, prev, naturalRec
> 
>   , _test_nats, main_nats
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import DisjointUnions
> import Unary

We have assumed the existence of a set $\nats$ such that there is a unique inductive set homomorphism from $\nats$ to any other inductive set. But it turns out that this set is not *unique* with this property; any other inductive set which is *isomorphic* to $\nats$ enjoys it as well. In fact we've already seen one such set, namely $1 + \nats$.

Here's a handwavy proof. Let $(A,\varphi,e)$ be an inductive set, and suppose the unique map $\theta : \nats \rightarrow A$ is bijective. Then there is a unique inductive set homomorphism $\omega : A \rightarrow \nats$; namely, $\omega = \theta^{-1}$. Now any homomorphism from $A$ factors through the (unique) map $\omega$.

From a mathematical point of view, isomorphic objects are interchangeable. But as we'll eventually see, from a *computational* point of view, isomorphic objects can behave very differently. For this reason we will think of the properties of $\nats$ as a kind of interface, and write our programs against that. Specifically, every element of a $\nats$-like set is either the zero or the successor of some other element, and $\unnext$ discriminates between the two.

Now every inductive set isomorphic to $\nats$ is characterized by (1) its zero element, (2) its successor function, (3) the unique map $A \rightarrow \nats$, and (4) the unique map $\nats \rightarrow A$. We will also need a helper function to recognize the shape of a natural number, and for convenience a helper to convert a Haskell-native ``Integer`` to a natural number.

> class Natural n where
>   zero :: n
> 
>   next :: n -> n
> 
>   unnext :: n -> Either () n
>   
>   natural :: Integer -> n

Our helpers $\iszero$ and $\prev$ can be written against this interface:

> isZero :: (Natural n) => n -> Bool
> isZero = (either (const true) (const false)) . unnext
> 
> prev :: (Natural n) => n -> n
> prev = (either (const zero) id) . unnext

As can the natural recursion operator $\natrec{\ast}{\ast}$.

> naturalRec :: (Natural n)
>   => a -> (a -> a) -> n -> a
> naturalRec e phi n =
>   let
>     tau !x k = case unnext k of
>       Left () -> x
>       Right m -> tau (phi x) m
>   in tau e n

From now on we'll write programs against the ``Natural`` interface with ``naturalRec`` instead of ``Unary`` specifically. Of course, ``Unary`` is an instance of ``Natural``:

> instance Natural Unary where
>   zero = Z
> 
>   next = N
> 
>   unnext k = case k of
>     Z   -> Left ()
>     N m -> Right m
> 
>   natural = mkUnary

Okay!


Testing
-------

We proved some theorems about $\unnext$, $\prev$, and $\iszero$ in the last post.

> _test_unnext_zero :: (Natural n, Equal n)
>   => n -> Test Bool
> _test_unnext_zero m =
>   testName "unnext(0) == lft(*)" $
>   eq
>     (unnext (zero `withTypeOf` m))
>     (lft ())
> 
> 
> _test_unnext_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_unnext_next _ =
>   testName "unnext(next(m)) == rgt(m)" $
>   \m -> eq (unnext (next m)) (rgt m)
> 
> 
> _test_prev_zero :: (Natural n, Equal n)
>   => n -> Test Bool
> _test_prev_zero m =
>   testName "prev(0) == 0" $
>   eq
>     (prev (zero `withTypeOf` m))
>     zero
> 
> 
> _test_prev_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_prev_next _ =
>   testName "prev(next(m)) == m" $
>   \m -> eq (prev (next m)) m
> 
> 
> _test_isZero_zero :: (Natural n, Equal n)
>   => n -> Test Bool
> _test_isZero_zero m =
>   testName "isZero(0) == true" $
>   eq
>     (isZero (zero `withTypeOf` m))
>     true
> 
> 
> _test_isZero_next :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_isZero_next _ =
>   testName "isZero(next(m)) == false" $
>   \m -> eq (isZero (next m)) false


Suite.

> _test_nats :: (TypeName n, Natural n, Show n, Arbitrary n, Equal n)
>   => n -> Int -> Int -> IO ()
> _test_nats n maxSize numCases = do
>   testLabel1 "nats" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_unnext_zero n)
>   runTest args (_test_unnext_next n)
>   runTest args (_test_prev_zero n)
>   runTest args (_test_prev_next n)
>   runTest args (_test_isZero_zero n)
>   runTest args (_test_isZero_next n)

Main.

> main_nats :: IO ()
> main_nats = do
>   _test_nats (zero :: Unary) 100 100
