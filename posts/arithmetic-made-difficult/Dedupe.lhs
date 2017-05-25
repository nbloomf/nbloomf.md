---
title: Dedupe
author: nbloomf
date: 2017-05-26
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE ScopedTypeVariables #-}
> module Dedupe
>   ( dedupeL, dedupeR, _test_dedupe, main_dedupe
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

Today we'll define a function ``dedupe`` which removes any "duplicate" items in a list. Before jumping in, let's think a little about what such a function should do. For example, say we run ``dedupe`` on the list $$\langle a, b, a, c, a \rangle.$$ The item $a$ appears three times, so after deduplicating it should only appear once. We'd prefer not to change the relative order of items in the list, so all we can do is remove two of the $a$s. There are three ways to do this, resulting in either $$\langle a, b, c \rangle,$$ $$\langle b, a, c \rangle,$$ or $$\langle b, c, a \rangle.$$ That is, we can keep the *first* copy of $a$, the *last* copy, or *some middle* copy. It seems to me that keeping some middle copy is not the most general solution. If an item appears only twice, there is no middle appearance, and if an item appears more than three times then there is no *unique* middle appearance to keep. So it appears the two most general options are to keep the first copy of an item or to keep the last copy. We will call these strategies $\dedupeL$ (**dedup**licate from the **L**eft) and $\dedupeR$ (**dedup**licate from the **R**ight), respectively. We'll see that these two options are related. We'll start with $\dedupeL$.

We want to implement $\dedupeL$ as either a right fold or a left fold. But which one? Say our input list is $$x = \langle a, b, c \rangle.$$ Note that $\foldr{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(a, \varphi(b, \varphi(c, \varepsilon))),$$ while $\foldl{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(c, \varphi(b, \varphi(a, \varepsilon))).$$ Note that $\dedupeL$ has to process the entire input list, so both of these computations will evaluate completely from the inside out. So which one makes more sense, keeping in mind that $\dedupeL$ needs to detect the *first* appearance of each item?

To my eye it seems that ``foldl`` is a natural choice here, since the accumulating parameter can keep track of whether a given item has been seen and $\varphi$ can use this information to decide whether each new item should be kept or not. The big remaining question is what exactly to do with the accumulating parameter. It should have type $\lists{A}$, and $\varphi$ will somehow add new items to it -- the two ways to do this are with $\cons$ and $\snoc$. $\snoc$ is certainly correct here, but much slower than $\cons$. The only problem is that $\cons$ will end up reversing the order of the input list -- not what we want. But this can be fixed by just putting the output through $\rev$.

With this handwavy mess in mind, we define $\dedupeL$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(a,x) = \bif{\elt(a,x)}{x}{\cons(a,x)}.$$ Now define $\dedupeL : \lists{A} \rightarrow \lists{A}$ by $$\dedupeL(x) = \rev(\foldl{\nil}{\varphi}(x)).$$

In Haskell:

> dedupeL :: (List t, Equal a) => t a -> t a
> dedupeL = rev . foldl nil phi
>   where
>     phi a x = if elt a x then x else cons a x

</p></div>
</div>

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

> dedupeR :: (List t, Equal a) => t a -> t a
> dedupeR = rev . dedupeL . rev

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
> _test_dedupeL_unique :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_dedupeL_unique _ x =
>    (unique (dedupeL x)) ==== True
> 
> 
> -- dedupeL(dedupeL(x)) == dedupeL(x)
> _test_dedupeL_involution :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_dedupeL_involution _ x =
>    (dedupeL (dedupeL x)) ==== (dedupeL x)
> 
> 
> -- prefix(x,y) ==> prefix(dedupeL(x),dedupeL(y))
> _test_dedupeL_prefix :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_dedupeL_prefix _ x y =
>    if prefix x y
>      then prefix (dedupeL x) (dedupeL y)
>      else True

And the suite:

> -- run all tests for dedupe & unique
> _test_dedupe ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_dedupe t maxSize numCases = do
>   testLabel ("dedupeL & dedupeR & unique: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_dedupeL_unique t)
>   runTest args (_test_dedupeL_involution t)
>   runTest args (_test_dedupeL_prefix t)

And ``main``:

> main_dedupe :: IO ()
> main_dedupe = do
>   _test_dedupe (nil :: ConsList Bool)  20 100
>   _test_dedupe (nil :: ConsList Unary) 20 100
