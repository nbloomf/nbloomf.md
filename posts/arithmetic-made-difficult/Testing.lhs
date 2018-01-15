---
title: Arithmetic Made Difficult
author: nbloomf
date: 2018-01-12
tags: arithmetic-made-difficult, literate-haskell
---

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

One of our main uses for ``Bool`` will be checking the results of tests, so this is as good a place as any to introduce a couple of QuickCheck helper functions for this.

> type Test prop = (String, prop)
> 
> testName :: String -> prop -> Test prop
> testName name prop = (name, prop)
> 
> runTest :: Testable prop => Args -> Test prop -> IO ()
> runTest args (name, prop) = do
>   putStrLn ("\x1b[1;34m" ++ name ++ "\x1b[0;39;49m")
>   result <- quickCheckWithResult args prop
>   if isSuccess result
>     then return ()
>     else putStrLn (show result) >> exitFailure
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\n\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
> 
> testLabel0 :: String -> IO ()
> testLabel0 = testLabel
> 
> testLabel1 :: (TypeName a) => String -> a -> IO ()
> testLabel1 str a = testLabel $ concat
>   [ str, ": ", typeName a ]
> 
> testLabel2 :: (TypeName a, TypeName b) => String -> a -> b -> IO ()
> testLabel2 str a b = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b ]
> 
> testLabel3 :: (TypeName a, TypeName b, TypeName c) => String -> a -> b -> c -> IO ()
> testLabel3 str a b c = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b, ", ", typeName c ]
>
> 
> withTypeOf :: a -> a -> a
> withTypeOf x _ = x
> 
> class TypeName t where
>   typeName :: t -> String
> 
> instance TypeName Bool where
>   typeName _ = "Bool"
