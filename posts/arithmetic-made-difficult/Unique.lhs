---
title: Unique
author: nbloomf
date: 2017-05-25
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE ScopedTypeVariables #-}
> module Unique
>   ( unique, _test_unique, main_unique
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
> import Sublist
> 
> import Prelude (uncurry)
> import Test.QuickCheck
> import Text.Show.Functions

We'd like to also prove some properties for $\dedupeL$. The most important one -- and the reason for introducing ``dedupe`` -- is that $\dedupeL(x)$ should not have any duplicated items. We'll introduce a boolean function $\unique$ to detect whether or not this is the case. As usual, we'd like to define $\unique$ as a fold.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times (\bool \times \lists{A}) \rightarrow \bool \times \lists{A}$ by $$\varphi(a,(p,x)) = \left\{ \begin{array}{ll} (\bfalse,\nil) & \mathrm{if}\ \elt(a,x) \\ (\btrue,\cons(a,x)) & \mathrm{otherwise}. \end{array}\right.$$ Now define $\unique : \lists{A} \rightarrow \bool$ by $$\unique(x) = \fst(\foldr{(\btrue,\nil)}{\varphi}(x)).$$

In Haskell (we have to use the ``ScopedTypeVariables`` extension and provide some extra type signatures here to write this in the obvious way):

> unique :: forall t a. (List t, Equal a) => t a -> Bool
> unique = fst . foldr (True, nil :: t a) phi
>   where
>     phi :: (List t, Equal a) => a -> (Bool, t a) -> (Bool, t a)
>     phi a (p,x) = if elt a x
>       then (False, nil)
>       else (True,  cons a x)

</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$, the following are equivalent.

1. $\unique(x) = \btrue$.
2. If $i,j \in \nats$ such that $\at(x,i), \at(x,j) \in A$ and $i \neq j$ then $\at(x,i) \neq \at(x,j)$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \unique(\nil) \\
 & = & \fst(\foldr{(\btrue,\nil)}{\varphi}(\nil)) \\
 & = & \fst(\btrue,\nil) \\
 & = & \btrue.
\end{eqnarray*}$$
Now note that $\at(\nil,i)$ is $\ast$ for all $i$, and thus when $x = \nil$ statement (2) is vacuously true. Thus (1) is equivalent to (2).

For the inductive step, suppose the equivalence holds for some $x$ and let $a \in A$. (@@@)
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
Let $A$ be a set. Define $\dedupeL : \lists{A} \rightarrow \lists{A}$ by $$\dedupeL(x) = \rev(\dedupeR(\rev(x))).$$

In Haskell:

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

Here are our property tests for $\unique$:

> -- unique(dedupeL(x)) == true
> _test_unique_rev :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_unique_rev _ x =
>    (unique x) ==== (unique (rev x))

And the suite:

> -- run all tests for unique
> _test_unique ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_unique t maxSize numCases = do
>   testLabel ("unique: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_unique_rev t)

And ``main``:

> main_unique :: IO ()
> main_unique = do
>   _test_unique (nil :: ConsList Bool)  20 100
>   _test_unique (nil :: ConsList Unary) 20 100
