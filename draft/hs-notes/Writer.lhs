---
title: Writer
author: nbloomf
date: 2018-05-26
tags: hs-notes, literate-haskell
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Writer where
> 
> import Monad
> 
> import Prelude
>   ( IO, Functor(..), Applicative(..), Monad(..), Monoid(..), Eq(..), Show(..), Bool, Int, Char, (&&), ($), (.), (++)
>   )
> import Data.Proxy
> import Text.Show.Functions
> 
> import Test.QuickCheck

> data Writer w a = Writer w a

> instance (Eq w, Eq a) => Eq (Writer w a) where
>   (Writer w a) == (Writer v b) = (w == v) && (a == b)

> instance (Show w, Show a) => Show (Writer w a) where
>   show (Writer w a) = "Writer " ++ show w ++ " " ++ show a

> instance Functor (Writer w) where
>   fmap f (Writer w a) = Writer w (f a)

> instance (Monoid w) => Applicative (Writer w) where
>   pure a = Writer mempty a
> 
>   (Writer w1 f) <*> (Writer w2 a) =
>     Writer (mappend w1 w2) (f a)

> instance (Monoid w) => Monad (Writer w) where
>   return = pure
> 
>   (Writer w1 a) >>= f =
>     let Writer w2 b = f a in
>     Writer (mappend w1 w2) b

> writer :: (w,a) -> Writer w a
> writer (w,a) = Writer w a

> tell :: w -> Writer w ()
> tell w = Writer w ()

> listen :: Writer w a -> Writer w (w,a)
> listen (Writer w a) = Writer w (w,a)

> pass :: Writer w (a, w -> w) -> Writer w a
> pass (Writer w (a, f)) = Writer (f w) a

> writer_tell_hom
>   :: ( Monoid w, Eq w )
>   => Proxy w
>   -> w -> w -> Bool
> writer_tell_hom _ u v =
>   (tell u >> tell v) == (tell (mappend u v))

> instance (Monoid w, Arbitrary w, Arbitrary a) => Arbitrary (Writer w a) where
>   arbitrary = do
>     a <- arbitrary
>     w <- arbitrary
>     return (Writer w a)

> test = quickCheck $ monad_law_left_identity (Proxy :: Proxy (Writer [Bool])) (Proxy :: Proxy Bool) (Proxy :: Proxy Bool)

> test_main :: IO ()
> test_main = do
>   monad_laws_test_cases (Proxy :: Proxy (Writer ()))
>   monad_laws_test_cases (Proxy :: Proxy (Writer [Bool]))
>   monad_laws_test_cases (Proxy :: Proxy (Writer [Int]))
> 
>   quickCheck $ writer_tell_hom (Proxy :: Proxy [Bool])
