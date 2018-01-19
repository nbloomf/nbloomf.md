---
title: Arithmetic Made Difficult
author: nbloomf
date: 2018-01-12
tags: arithmetic-made-difficult, literate-haskell
slug: testing
---

Proving that programs are correct is hard. For one thing, determining what it means for a program to be "correct" is not trivial -- it always has a certain output? never has an error? doesn't do unnecessary work? what is the execution model? But programs can be very useful things, and assurance that they are "correct" (whatever that means) may be valuable.

Comparatively, proving theorems in mathematics is easy. In algebra especially lots of proofs can be written in the so-called "equational" style, which is straightforward to the point of boringness. In this style of proof we can establish that $A$ is equal to $B$ by producing a sequence of statements, each equal to the next according to strict rules, starting at $A$ and ending at $B$.

So we have on the one hand some programs we'd like to prove things about, and on the other a simple proof technique. With some careful thought, we can apply one to the other -- we just have to get used to thinking of programs as *arithmetic* in an appropriate *algebra*.

This is an old idea, and many books have been written about it. In this series of posts I'll be exploring this idea for myself. In a nutshell, different kinds of data structures can be thought of as elements of an algebra with a universal property. The prototype for this point of view is the natural numbers; the universal property is essentially the principle of mathematical induction, and we can use it to define the usual arithmetic on numbers. This process generalizes to other kinds of structures, and "arithmetic" generalizes to *programs*. And just like induction is the power tool for proving things about the natural numbers, generalized induction can be used to prove things about other structures.

We can build an *algebra of programs*.


Testing
-------

Along the way we'll see lots of identities. These are equations that are true for all possible values of any variables, like $$a + b = b + a$$ where $a$ and $b$ are integers. Although we'll establish these with proof, identities are prime candidates for checking with *generative tests*. If an equation like $a+b = b+a$ is supposed to be true for all possible $a$ and $b$, one way to test this is to generate a bunch of random pairs and see if the equation holds.

We'll use the ``QuickCheck`` library to make our theorems testable. This is not the same as making our proofs machine-checkable, but can still be a useful tool for finding bugs. This module reexports just enough of ``QuickCheck`` for our needs.

> {-# LANGUAGE NoImplicitPrelude #-}
> module Testing
>   ( Test, runTest, testName, withTypeOf, TypeName(..)
>   , testLabel0, testLabel1, testLabel2, testLabel3
> 
>   , module Prelude
>   , module Test.QuickCheck
>   , module Test.QuickCheck.Test
> ) where
> 
> 
> import Prelude
>   ( Show(show), IO, Bool(), Int, Maybe(..), Either(..), id, undefined, concat
>   , putStrLn, (>>), return, (++), String, (.), ($), Integer, const, uncurry
>   )
> import Test.QuickCheck
>   ( Testable(..), Args(..), Arbitrary(..), CoArbitrary(..)
>   , quickCheckWithResult, stdArgs, variant
>   )
> import Test.QuickCheck.Test (isSuccess)
> import Text.Show.Functions
> import System.Exit

The ``Test`` type, with ``testName``, is a shorthand for writing named tests.

> type Test prop = (String, prop)
> 
> testName :: String -> prop -> Test prop
> testName name prop = (name, prop)

``runTest`` runs a named test.

> runTest :: Testable prop => Args -> Test prop -> IO ()
> runTest args (name, prop) = do
>   putStrLn ("\x1b[1;34m" ++ name ++ "\x1b[0;39;49m")
>   result <- quickCheckWithResult args prop
>   if isSuccess result
>     then return ()
>     else putStrLn (show result) >> exitFailure

``TypeName``, ``testLabel``, and friends are used to print headers for test suites.

> class TypeName t where
>   typeName :: t -> String
> 
> instance TypeName Bool where
>   typeName _ = "Bool"
> 
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\n\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
> 
> testLabel0 :: String -> IO ()
> testLabel0 = testLabel
> 
> testLabel1 :: (TypeName a)
>   => String -> a -> IO ()
> testLabel1 str a = testLabel $ concat
>   [ str, ": ", typeName a ]
> 
> testLabel2 :: (TypeName a, TypeName b)
>   => String -> a -> b -> IO ()
> testLabel2 str a b = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b ]
> 
> testLabel3 :: (TypeName a, TypeName b, TypeName c)
>   => String -> a -> b -> c -> IO ()
> testLabel3 str a b c = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b, ", ", typeName c ]

``withTypeOf`` is used to enforce type constraints in tests. It makes more sense when you see some examples.

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x
