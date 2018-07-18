---
title: Managing Effects
author: nbloomf
date: 2018-05-25
tags: hs-notes, literate-haskell
---

What I like most about monads is that they offer a concrete and principled strategy for achieving what Paul Graham calls [bottom-up design](http://www.paulgraham.com/progbot.html). Quoting:

<blockquote>
Experienced Lisp programmers divide up their programs differently. As well as top-down design, they follow a principle which could be called bottom-up design-- changing the language to suit the problem... Instead of a single, monolithic program, you will get a larger language with more abstract operators, and a smaller program written in it.
<cite>Paul Graham, from <a href="http://www.paulgraham.com/progbot.html">On Lisp</a></cite>
</blockquote>

The mechanism for doing this in Lisp (i.e. macros) is one way to enlarge a language. The point here is that monads are another way. This is *not at all* a new insight; I'm just writing these ideas down for myself because I learn better that way and putting them on the internet so I don't lose them.


What is a language?
-------------------

Before talking about how monads enlarge a language, it makes sense to try to nail down exactly what a "language" is, in the context of programming a computer.

Deep down, every computer (mumble von Neumann architecture) is a machine that has a list of named memory cells -- state -- and a list of "instructions" that it responds to by manipulating the contents of those memory cells. Then a program is a list of instructions to be interpreted by the machine one after the other; the seqence of instructions as seen by the CPU is the control flow. This is what a computer *is*, really. Any meaning beyond that is in our heads.

(This is super handwavy, but I promise there's a point.)

Portability issues aside, two basic problems make it hard to program a computer at the instruction level:

1. State: how to organize it, when to access it, when to get rid of it, how to share it, how to *not* share it, how to reason about it over time
2. Control Flow: how to chunk instructions into larger semantic units and ensure these are used only in specific ways, how to reason about it

I claim that every language above assembly is an attempt to provide *semantic* mechanisms for managing the complexity of these two problems. Loops, conditionals, functions/methods/subroutines, switches, macros -- these are semantic units of control flow. Assignment, variables, constants, data structures, pointers, arguments, namespaces -- these are semantic units of state manipulation. Higher level languages provide a set of semantic units that map down to the machine level in a behavior-preserving way, the hope being that whatever problem we *really* want to solve is more easily mapped to those units than to the machine instructions directly.

What monads do -- much like Lisp's macros -- is provide a *simple*, *principled*, and *uniform* interface for extending the set of semantic units in our toolbox for manipulating state and control flow in a *granular* and *composable* way. In theory monads can be used in any language, but -- also like Lisp's macros -- it's much more natural to do so if the language is set up for it.


Atomic Monads
-------------

* `Maybe`: catastrophic failure
* `Either e`: recoverable failure
* `[]`: finite nondeterminism with backtracking
* `Logic`: infinite nondeterminism with backtracking
* `State s`: state
* `Reader e`: read-only state
* [`Writer w`](/posts/hs-notes/Writer.html): write-only state
* `Idemp`: idempotence

> {-# LANGUAGE NoImplicitPrelude #-}
> module Monad where
> 
> import Prelude
>   ( Eq(..), Monad(..), Show(..)
>   , IO, Bool, Int, Char
>   , ($), (++), putStrLn
>   )
> import Data.Proxy
> import Data.Typeable
> import Text.Show.Functions
> import Control.Monad (unless)
> import System.Exit (exitFailure)
> 
> import Test.QuickCheck
> import Test.QuickCheck.Test (isSuccess)

> monad_law_right_identity
>   :: (Monad m, Eq (m a))
>   => Proxy m -> Proxy a
>   -> m a -> Bool
> 
> monad_law_right_identity _ _ x =
>   (x >>= return) == x

> monad_law_left_identity
>   :: (Monad m, Eq (m b))
>   => Proxy m -> Proxy a -> Proxy b
>   -> a -> (a -> m b) -> Bool
> 
> monad_law_left_identity _ _ _ a f =
>   (return a >>= f) == (f a)

> monad_law_associativity
>   :: (Monad m, Eq (m c))
>   => Proxy m -> Proxy a -> Proxy b -> Proxy c
>   -> m a -> (a -> m b) -> (b -> m c) -> Bool
> 
> monad_law_associativity _ _ _ _ x f g =
>   ((x >>= f) >>= g) == (x >>= (\z -> f z >>= g))

> test_monad_laws
>   :: ( Monad m
>      , Eq (m a), Eq (m b), Eq (m c)
>      , Show a, Show (m a)
>      , Arbitrary a, CoArbitrary a, CoArbitrary b
>      , Arbitrary (m a), Arbitrary (m b), Arbitrary (m c)
>      , Typeable m, Typeable a, Typeable b, Typeable c
>      )
>   => Proxy m -> Proxy a -> Proxy b -> Proxy c
>   -> IO ()
> 
> test_monad_laws m a b c = do
>   let
>     k = 1000
>     label =
>       show (typeRep m) ++ ", " ++
>       show (typeRep a) ++ ", " ++
>       show (typeRep b) ++ ", " ++
>       show (typeRep c)
>   putStrLn $ "\x1b[35mChecking Monad Laws\x1b[0;39;49m"
>   putStrLn $ "\x1b[36m" ++ label ++ "\x1b[0;39;49m"
>   putStrLn $ "\x1b[32mRight Identity\x1b[0;39;49m"
>   result <- quickCheckResult $ withMaxSuccess k $ monad_law_right_identity m a
>   unless (isSuccess result) exitFailure
>   putStrLn $ "\x1b[32mLeft Identity\x1b[0;39;49m"
>   result <- quickCheckResult $ withMaxSuccess k $ monad_law_left_identity m a b
>   unless (isSuccess result) exitFailure
>   putStrLn $ "\x1b[32mAssociativity\x1b[0;39;49m"
>   result <- quickCheckResult $ withMaxSuccess k $ monad_law_associativity m a b c
>   unless (isSuccess result) exitFailure
>   return ()

> monad_laws_test_cases
>   :: ( Monad m, Typeable m
>      , Eq (m ()), Show (m ()), Arbitrary (m ())
>      , Eq (m Bool), Show (m Bool), Arbitrary (m Bool)
>      , Eq (m Int), Show (m Int), Arbitrary (m Int)
>      , Eq (m Char), Show (m Char), Arbitrary (m Char)
>      )
>   => Proxy m -> IO ()
> monad_laws_test_cases m = do
>   let
>     unit = Proxy :: Proxy ()
>     bool = Proxy :: Proxy Bool
>     int = Proxy :: Proxy Int
>     char = Proxy :: Proxy Char
> 
>   test_monad_laws m unit unit unit
> 
>   test_monad_laws m bool bool bool
> 
>   test_monad_laws m int int int
>   test_monad_laws m bool int int
>   test_monad_laws m int bool int
>   test_monad_laws m int int bool
>   test_monad_laws m int bool bool
>   test_monad_laws m bool int bool
>   test_monad_laws m bool bool int
> 
>   test_monad_laws m char char char
