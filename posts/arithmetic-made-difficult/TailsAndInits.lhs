---
title: Tails and Inits
author: nbloomf
date: 2017-05-12
tags: arithmetic-made-difficult, literate-haskell
---

> module TailsAndInits
>   ( tails, inits, _test_tails_inits, main_tails_inits
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, map, zip, all, any, tail)
> 
> import Lists
> import Reverse
> import Map
> import Cat
> import Zip
> import Prefix
> import AllAndAny
> 
> import Test.QuickCheck
> import Text.Show.Functions



<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\varepsilon(w) = \cons(w,\nil)$$ and define $\varphi : A \times \lists{\lists{A}}^{\lists{A}} \rightarrow \lists{\lists{A}}^{\lists{A}}$ by $$\varphi(a,f)(w) = \cons(w,f(\tails(w))).$$ Now define $\tails : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\tails(x) = \foldr{\varepsilon}{\varphi}(x)(x).$$
</p></div>
</div>

We can translate $\all$ to Haskell directly as follows:

> tails' :: (ListOf t) => t a -> t (t a)
> tails' x = foldr epsilon phi x x
>   where
>     epsilon w = cons w nil
>     phi a f w = cons w (f (tail w))

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$ we have the following.

1. $\tails(\nil) = \cons(\nil,\nil)$.
2. $\tails(\cons(a,x)) = \cons(\cons(a,x),\tails(x))$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>

In Haskell:

> tails :: (ListOf t) => t a -> t (t a)
> tails x = case listShape x of
>   Nil      -> cons nil nil
>   Cons a w -> cons (cons a x) (tails w)

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$ we have $$\tails(\map(f)(x)) = \map(\map(f))(\tails(x)).$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\tails(x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
(@@@)
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

> inits :: (ListOf t) => t a -> t (t a)
> inits x = map rev (tails (rev x))



Testing
-------

Here are our property tests for $\tails$ and $\inits$:

> -- tails(x) == tails'(x)
> _test_tails_alt :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_tails_alt _ x =
>   listEqBy listEq (tails x) (tails' x)

And the suite:

> -- run all tests for tails and inits
> _test_tails_inits :: (ListOf t, Arbitrary a, CoArbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_tails_inits t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_tails_alt t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_tails_inits :: IO ()
> main_tails_inits = _test_tails_inits (nil :: List Bool) 20 100
