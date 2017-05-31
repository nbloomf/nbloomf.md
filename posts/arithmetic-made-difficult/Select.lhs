---
title: Select
author: nbloomf
date: 2017-05-25
tags: arithmetic-made-difficult, literate-haskell
---

> module Select
>   ( _test_select, main_select
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
> import Prelude (uncurry)
> import Test.QuickCheck
> import Text.Show.Functions



<div class="result">
<div class="defn"><p>


In Haskell:


</p></div>
</div>



<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times (\bool \times \lists{A}) \rightarrow \bool \times \lists{A}$ by $$\varphi(a,(p,x)) = \left\{ \begin{array}{ll} (\bfalse,\nil) & \mathrm{if}\ \elt(a,x) \\ (\btrue,\cons(a,x)) & \mathrm{otherwise}. \end{array}\right.$$ Now define $\unique : \lists{A} \rightarrow \bool$ by $$\unique(x) = \fst(\foldr{(\btrue,\nil)}{\varphi}(x)).$$

In Haskell (we have to use the ``ScopedTypeVariables`` extension and provide some extra type signatures here to write this in the obvious way):



</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="defn"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>


Testing
-------

Here are our property tests for $\dedupeL$, $\dedupeR$, and $\unique$:

> -- unique(dedupeL(x)) == true
> _test_select_zero :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_select_zero _ x =
>    True
> 
> 

And the suite:

> -- run all tests for select
> _test_select ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_select t maxSize numCases = do
>   testLabel ("select: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_select_zero t)

And ``main``:

> main_select :: IO ()
> main_select = do
>   _test_select (nil :: ConsList Bool)  20 100
>   _test_select (nil :: ConsList Unary) 20 100
