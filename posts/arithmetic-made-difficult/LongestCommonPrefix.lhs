---
title: Longest Common Prefix
author: nbloomf
date: 2017-05-08
tags: arithmetic-made-difficult, literate-haskell
---

> module LongestCommonPrefix
>   ( lcp, lcs, _test_lcp, main_lcp
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, map, zip)
> 
> import Lists
> import Reverse
> import Cat
> import Zip
> import Prefix
> 
> import Test.QuickCheck



<div class="result">
<div class="defn"><p>

</p></div>
</div>

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>


Testing
-------

Here are our property tests for $\lcp$ and $\lcs$.

> -- prefix(x,cat(x,y))
> _test_prefix_cat :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_prefix_cat _ x y =
>   prefix x (cat x y)

And the suite:

> -- run all tests for lcp and lcs
> _test_lcp :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_lcp t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_prefix_cat t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_lcp :: IO ()
> main_lcp = _test_lcp (nil :: List Bool) 20 100
