---
title: Arithmetic Made Difficult
author: nbloomf
date: 2018-01-12
tags: arithmetic-made-difficult, literate-haskell
slug: testing
---

Proving that programs are correct is hard. For one thing, determining what it means for a program to _be_ correct is not trivial -- it always has a certain output? never has an error? doesn't do unnecessary work? what is the execution model? But programs can be very useful and expensive things, and any assurance that they do what we think they do is valuable.

Comparatively, proving theorems in mathematics is easy. In algebra especially lots of proofs can be written in the so-called "equational" style, which is straightforward to the point of boringness. In this style of proof we start with a list of *identities*; equalities between two expressions involving both *constants* and *variables* that we assume to be true for any values we might substitute for the variables. We then deduce more identities using a substitution rule. For example, we can think of the symbols $+$, $2$, and $3$ as constants, the symbols $a$ and $b$ as variables, and the expression $a + b = b + a$ as an identity. From this identity we can deduce the identity $2 + 3 = 3 + 2$, by making the substitution $a = 2$ and $b = 3$. This is a simple, one-step example, but the basic strategy is widely applicable -- the [Metamath](http://us.metamath.org/) project aims to formalize large chunks of mathematics using (more or less) this strategy. What's more, verifying that such proofs are valid can be done by pattern matching, using the identities as rewrite rules.

So we have on the one hand some programs we'd like to prove things about, and on the other a simple proof technique. With some careful thought, we can apply one to the other -- we just have to get used to thinking of programs as *arithmetic* in an appropriate *algebra*.

This is an old idea, and many books have been written about it. In this series of posts I'll be exploring this idea for myself. In a nutshell, different kinds of data structures can be thought of as elements of an algebra with a universal property. The prototype for this point of view is the natural numbers; the universal property is essentially the principle of mathematical induction, and we can use it to define the usual arithmetic on numbers. This process generalizes to other kinds of structures, and "arithmetic" generalizes to *programs*. And just like induction is the power tool for proving things about the natural numbers, generalized induction can be used to prove things in the equational style.

We can build an *algebra of programs*, and doing so has some interesting benefits.

* In algebra, interesting objects are often defined in terms of a *universal property*. Instead of defining an object in terms of what it _is_, a universal property characterizes an object by how it _behaves_. It's a very declarative way of thinking. This gives a simple, prepackaged way to detect when two programs are equivalent, such as a slow-but-obviously-correct one and a fast-but-not-obviously-correct one.
* Just as in ordinary arithmetic, many theorems come in the form of universally quantified equations. These are tailor made for _property-based_ or _generative_ testing.
* Equational proofs come with a simple strategy for verification: term rewriting. If we're careful about how we write proofs, individual steps can be mechanically verified by a simple tool.

We could do this using a language designed specifically for formal verification, but I'd like to stay as close to English as possible. At the same time, in any big list of proofs there's the danger that some of them are wrong. To help mitigate this I'll use two different kinds of checks. First, we'll implement our definitions in an executable language and include automated tests for as many theorems as possible. And second, as much as possible, we'll use a term rewriting tool to check that the steps in our equational proofs are correct. If you see a blue equals sign in an equational proof, that signifies a link to the previous theorem or definition which justifies the equality. But more than that, the blue equals signs are verified by an [automated tool](/posts/2018-01-22-a-simple-term-rewriting-tool.html).


Property Testing
----------------

I've chosen to write my executable definitions in Haskell, because that's what I'm most comfortable with, but that's just a choice -- many other languages would do. Many theorems will have a stackish flavor; something like Factor or J might also work well.

We'll use the ``QuickCheck`` library to make our theorems testable. This is not the same as making our proofs machine-checkable, but can still be a useful tool for finding bugs and checking assumptions. This module reexports just enough of ``QuickCheck`` for our needs.

> {-# LANGUAGE NoImplicitPrelude #-}
> module Testing
>   ( Test, runTest, testName, withTypeOf, TypeName(..)
>   , labelTestArgs1
>   , testLabel0, testLabel1, testLabel2, testLabel3, testArgs
> 
>   , Equal(..)
> 
>   , module Prelude
>   , module Test.QuickCheck
>   , module Test.QuickCheck.Test
>   , module Data.Proxy
>   , module Data.Typeable
> ) where
> 
> 
> import Prelude
>   ( Show(show), IO, Int, undefined, concat, Bool(..)
>   , putStrLn, (>>), (>>=), return, (++), String, (.), ($), Integer
>   )
> import Test.QuickCheck
>   ( Testable(..), Args(..), Arbitrary(..), CoArbitrary(..)
>   , quickCheckWithResult, stdArgs, variant
>   )
> import Test.QuickCheck.Test (isSuccess)
> import Data.Proxy (Proxy(..))
> import Data.Typeable (Typeable, typeRep)
> import Text.Show.Functions ()
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
> instance TypeName () where
>   typeName _ = "()"
> 
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\n\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
> 
> testLabel0 :: String -> IO ()
> testLabel0 = testLabel
> 
> labelTestArgs1 :: (Typeable a)
>   => String -> Proxy a -> IO ()
> labelTestArgs1 str a = testLabel $ concat
>   [ str, ": ", show $ typeRep a ]
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
> 
> testArgs :: Int -> Int -> Args
> testArgs size cases = stdArgs
>   { maxSuccess = cases, maxSize = size }

``withTypeOf`` is used to enforce type constraints in tests. It makes more sense when you see some examples.

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x


Equality
--------

To write tests, we also need a notion of "equality" for values. This is a little out of order -- we'll define the boolean truth values in a later post -- but we need equality now, so I'll put the definition here. Typically I think of equality (as in the $=$ symbol) as a metalanguage expression anyway.

> class Equal a where
>   eq :: a -> a -> Bool

(Why not use the built in `Eq` class? No good reason.) We'll implement ``Equal`` for new types as we encounter them. For now we need two: ``Bool`` and ``()``.

> instance Equal Bool where
>   eq True  True  = True
>   eq True  False = False
>   eq False True  = False
>   eq False False = True
> 
> instance Equal () where
>   eq () () = True

All our instances of `Equal` will be assumed to satisfy the following.

:::::: axiom :::::::
[]{#thm-eq-reflexive}[]{#thm-eq-symmetric}
Let $A$ be a set.

1. For all $a \in A$, we have $\beq(a,a) = \btrue$.
2. For all $a,b \in A$, we have $\beq(a,b) = \beq(b,a)$.
::::::::::::::::::::
