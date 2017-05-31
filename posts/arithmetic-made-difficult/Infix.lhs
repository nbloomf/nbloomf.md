---
title: Infix
author: nbloomf
date: 2017-05-24
tags: arithmetic-made-difficult, literate-haskell
---

> module Infix
>   ( isInfix, _test_isInfix, main_isInfix
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions



<div class="result">
<div class="defn"><p>

</p></div>
</div>

We can translate the definition of $\sublist$ to Haskell:

> sublist' :: (List t, Equal a) => t a -> t a -> Bool
> sublist' x y = foldr isNil phi y x
>   where
>     phi a f w = case listShape w of
>       Nil      -> True
>       Cons b u -> if eq a b then f u else f w

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

In Haskell:

> sublist :: (List t, Equal a) => t a -> t a -> Bool
> sublist x y = case listShape x of
>   Nil      -> True
>   Cons a u -> case listShape y of
>     Nil      -> False
>     Cons b v -> if eq a b
>       then sublist u v
>       else sublist x v

A lemma.

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>


Testing
-------

Here are our property tests for $\infix$:

> -- sublist'(x,y) == sublist(x,y)
> _test_sublist_alt :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_alt _ x y =
>    (sublist' x y) ==== (sublist x y)

And the suite:

> -- run all tests for infix
> _test_isInfix ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_isInfix t maxSize numCases = do
>   testLabel ("sublist: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_sublist_alt t)

And ``main``:

> main_isInfix :: IO ()
> main_isInfix = do
>   _test_isInfix (nil :: ConsList Bool)  30 200
>   _test_isInfix (nil :: ConsList Unary) 30 200
