---
title: Repeat
author: nbloomf
date: 2017-05-22
tags: arithmetic-made-difficult, literate-haskell
---

> module Repeat
>   ( repeat, _test_repeat, main_repeat
>   ) where
> 
> import Booleans
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
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

So far we've defined a bunch of functions that operate on lists, but still only one that can create one out of nothing, namely $\range$. ($\tails$ and $\inits$ create lists, but only if we have one to start with.) Today we'll nail down another list-creating utility, $\repeat$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, and define $f : A \rightarrow \ast + A times A$ by $f(x) = (x,x)$. Now define $\repeat : \nats \times A \rightarrow \lists{A}$ by $$\repeat(n,a) = \unfoldN(f,n,a).$$
</p></div>
</div>

We can implement $\repeat$ in Haskell using the definition:

> repeat' :: (List t, Equal a, Natural n) => n -> a -> t a
> repeat' n a = unfoldN f n a
>   where
>     f x = Just (x,x)

But the next result suggests another way.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $k \in \nats$ we have the following.

1. $\repeat(\zero,a) = \nil$.
2. $\repeat(\next(k),a) = \cons(a,\repeat(k,a))$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>

In Haskell:

> repeat :: (List t, Equal a, Natural n) => n -> a -> t a
> repeat n a = case natShape n of
>   Zero   -> nil
>   Next k -> cons a (repeat k a)

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $n \in \nats$ and $a \in A$ we have $$\length(\repeat(n,a)) = n.$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $n \in \nats$ and $a \in A$, we have $$\repeat(n,f(a)) = \map(f)(\repeat(n,a)).$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $m,n \in \nats$ and $a \in A$, we have $$\repeat(\nplus(m,n),a) = \cat(\repeat(m,a),\repeat(n,a)).$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $n \in \nats$ and $a \in A$, we have the following.

1. $\snoc(a,\repeat(n,a)) = \repeat(\next(n),a).$$
2. $\rev(\repeat(n,a)) = \repeat(n,a)$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>


Testing
-------

Here are our property tests for $\repeat$:

> -- repeat'(n,a) == repeat(n,a)
> _test_repeat_alt :: (List t, Equal a, Natural n)
>   => t a -> n -> Nat n -> a -> Bool
> _test_repeat_alt t _ k a =
>  let
>    rna = repeat k a `withTypeOf` ListOf t
>  in
>    (repeat' k a) ==== rna
> 
> 
> -- length(repeat(n,a)) == n
> _test_repeat_length :: (List t, Equal a, Natural n)
>   => t a -> n -> Nat n -> a -> Bool
> _test_repeat_length t _ k a =
>  let
>    rna = repeat k a `withTypeOf` ListOf t
>  in
>    (length rna) ==== k

And the suite:

> -- run all tests for repeat
> _test_repeat ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Arbitrary n, Show n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_repeat t n maxSize numCases = do
>   testLabel ("repeat: " ++ typeName t ++ " & " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_repeat_alt t n)
>   runTest args (_test_repeat_length t n)

And ``main``:

> main_repeat :: IO ()
> main_repeat = do
>   _test_repeat (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_repeat (nil :: ConsList Unary) (zero :: Unary) 20 100
