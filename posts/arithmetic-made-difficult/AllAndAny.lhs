---
title: All and Any
author: nbloomf
date: 2017-05-10
tags: arithmetic-made-difficult, literate-haskell
---

> module AllAndAny
>   ( all, any, _test_all_any, main_all_any
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, map, zip, all, any)
> 
> import Lists
> import Reverse
> import Cat
> import Zip
> import Prefix
> 
> import Test.QuickCheck
> import Text.Show.Functions



<div class="result">
<div class="defn"><p>

</p></div>
</div>

We can translate $\all$ to Haskell directly as follows:

> all' :: (ListOf t) => (a -> Bool) -> t a -> Bool
> all' p = foldr epsilon (phi p)
>   where
>     epsilon = True
> 
>     phi p a q = if p a == True
>       then q
>       else False

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

In Haskell:

> all :: (ListOf t) => (a -> Bool) -> t a -> Bool
> all p x = case listShape x of
>   Nil      -> True
>   Cons a w -> (p a) && (all p w)



<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

> any :: (ListOf t) => (a -> Bool) -> t a -> Bool
> any p x = case listShape x of
>   Nil      -> False
>   Cons a w -> (p a) || (any p w)



Testing
-------

Here are our property tests for $\all$:

> -- all(p,cat(x,y)) == all(p,x) && all(p,y)
> _test_all_cat :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> t a -> Bool
> _test_all_cat _ p x y =
>   (all p (cat x y)) == ((all p x) && (all p y))
> 
> 
> -- all(p,rev(x)) == all(p,x)
> _test_all_rev :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> t a -> Bool
> _test_all_rev _ p x y =
>   (all p (rev x)) == (all p x)

Tests for $\any$:

> -- any(p,cat(x,y)) == any(p,x) || any(p,y)
> _test_any_cat :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> t a -> Bool
> _test_any_cat _ p x y =
>   (any p (cat x y)) == ((any p x) || (any p y))
> 
> 
> -- any(p,rev(x)) == any(p,x)
> _test_any_rev :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> t a -> Bool
> _test_any_rev _ p x y =
>   (any p (rev x)) == (any p x)

And the suite:

> -- run all tests for all and any
> _test_all_any :: (ListOf t, Arbitrary a, CoArbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_all_any t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_all_cat t)
>   , quickCheckWith args (_test_all_rev t)
> 
>   , quickCheckWith args (_test_any_cat t)
>   , quickCheckWith args (_test_any_rev t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_all_any :: IO ()
> main_all_any = _test_all_any (nil :: List Bool) 20 100
