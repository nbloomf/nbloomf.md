---
title: Dedupe
author: nbloomf
date: 2017-05-28
tags: arithmetic-made-difficult, literate-haskell
---

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
> import Select
> import Unique
> import Delete
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define a function ``dedupe`` which removes any "duplicate" items in a list. Before jumping in, let's think a little about what such a function should do. For example, say we run ``dedupe`` on the list $$\langle a, b, a, c, a \rangle.$$ The item $a$ appears three times, so after deduplicating it should only appear once. We'd prefer not to change the relative order of items in the list, so all we can do is remove two of the $a$s. There are three ways to do this, resulting in either $$\langle a, b, c \rangle,$$ $$\langle b, a, c \rangle,$$ or $$\langle b, c, a \rangle.$$ That is, we can keep the *first* copy of $a$, the *last* copy, or *some middle* copy. It seems to me that keeping some middle copy is not the most general solution. If an item appears only twice, there is no middle appearance, and if an item appears more than three times then there is no *unique* middle appearance to keep. So it appears the two most general options are to keep the first copy of an item or to keep the last copy. We will call these strategies $\dedupeL$ (**dedup**licate from the **L**eft) and $\dedupeR$ (**dedup**licate from the **R**ight), respectively. We'll see that these two options are related. We'll start with $\dedupeL$.

We want to implement $\dedupeL$ as either a right fold or a left fold. But which one? Say our input list is $$x = \langle a, b, c \rangle.$$ Note that $\foldr{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(a, \varphi(b, \varphi(c, \varepsilon))),$$ while $\foldl{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(c, \varphi(b, \varphi(a, \varepsilon))).$$ Note that $\dedupeL$ has to process the entire input list, so both of these computations will evaluate completely from the inside out. So which one makes more sense, keeping in mind that $\dedupeL$ needs to detect the *first* appearance of each item?

With this handwavy mess in mind, we define $\dedupeL$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(a,x) = \cons(a,\delete(a,x)).$$ Now define $\dedupeL : \lists{A} \rightarrow \lists{A}$ by $$\dedupeL(x) = \foldr{\nil}{\varphi}(x).$$

In Haskell:

> dedupeL :: (List t, Equal a) => t a -> t a
> dedupeL = foldr nil phi
>   where
>     phi a x = cons a (delete a x)

</p></div>
</div>

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\dedupeL(\nil) = \nil$.
2. $\dedupeL(\cons(a,x)) = \cons(a,\delete(a,\dedupeL(x)))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \dedupeL(\nil) \\
 & = & \foldr{\nil}{\varphi}(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \dedupeL(\cons(a,x)) \\
 & = & \foldr{\nil}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\nil}{\varphi}(x)) \\
 & = & \varphi(a,\dedupeL(x)) \\
 & = & \cons(a,\delete(a,\dedupeL(x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> dedupeL' :: (List t, Equal a) => t a -> t a
> dedupeL' x = case listShape x of
>   Nil      -> nil
>   Cons a u -> cons a (delete a (dedupeL' u))

Now $\dedupeL$ and $\delete$ commute.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x \in \lists{A}$. Then $$\delete(a,\dedupeL(x)) = \dedupeL(\delete(a,x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\nil)) \\
 & = & \delete(a,\nil) \\
 & = & \nil \\
 & = & \dedupeL(\nil) \\
 & = & \dedupeL(\delete(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$ and let $b \in A$. We consider two possibilities. If $b = a$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\cons(b,x))) \\
 & = & \delete(a,\cons(b,\delete(b,\dedupeL(x)))) \\
 & = & \delete(a,\delete(b,\dedupeL(x))) \\
 & = & \delete(a,\delete(a,\dedupeL(x))) \\
 & = & \delete(a,\dedupeL(x)) \\
 & = & \dedupeL(\delete(a,x)) \\
 & = & \dedupeL(\delete(a,\cons(a,x))) \\
 & = & \dedupeL(\delete(a,\cons(b,x)))
\end{eqnarray*}$$
as needed. Suppose instead that $b \neq a$. Now we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\cons(b,x))) \\
 & = & \delete(a,\cons(b,\delete(b,\dedupeL(x)))) \\
 & = & \cons(b,\delete(a,\delete(b,\dedupeL(x)))) \\
 & = & \cons(b,\delete(b,\delete(a,\dedupeL(x)))) \\
 & = & \cons(b,\delete(b,\dedupeL(\delete(a,x)))) \\
 & = & \dedupeL(\cons(b,\delete(a,x))) \\
 & = & \dedupeL(\delete(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\dedupeL$s are $\unique$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$. Then $\unique(\dedupeL(x)) = \btrue$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

$\dedupeL$ preserves $\prefix$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. If $\prefix(x,y) = \btrue$ then $\prefix(\dedupeL(x),\dedupeL(y)) = \btrue$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

$\dedupeL$ fixes $\unique$s.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x \in \lists{A}$. Then $\eq(x,\dedupeL(x)) = \unique(x)$.
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

Here are our property tests for $\dedupeL$ and $\dedupeR$:

> _test_dedupeL_alt :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_dedupeL_alt _ =
>   testName "dedupeL(x) == dedupeL'(x)" $
>   \x -> (dedupeL x) ==== (dedupeL' x)
> 
> 
> _test_dedupeL_unique :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_dedupeL_unique _ =
>   testName "unique(dedupeL(x)) == true" $
>   \x -> (unique (dedupeL x)) ==== True
> 
> 
> _test_dedupeL_delete :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> Bool)
> _test_dedupeL_delete _ =
>   testName "dedupeL(delete(a,x)) == delete(a,dedupeL(x))" $
>   \a x -> (dedupeL (delete a x)) ==== (delete a (dedupeL x))
> 
> 
> _test_dedupeL_involution :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_dedupeL_involution _ =
>   testName "dedupeL(dedupeL(x)) == dedupeL(x)" $
>   \x -> (dedupeL (dedupeL x)) ==== (dedupeL x)
> 
> 
> _test_dedupeL_eq_unique :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_dedupeL_eq_unique _ =
>   testName "eq(x,dedupeL(x)) == unique(x)" $
>   \x -> (eq x (dedupeL x)) ==== (unique x)
> 
> 
> _test_dedupeL_prefix :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_dedupeL_prefix _ =
>   testName "prefix(x,y) ==> prefix(dedupeL(x),dedupeL(y))" $
>   \x y -> if prefix x y
>     then prefix (dedupeL x) (dedupeL y)
>     else True

And the suite:

> -- run all tests for dedupe & unique
> _test_dedupe ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_dedupe t maxSize numCases = do
>   testLabel ("dedupeL & dedupeR: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_dedupeL_alt t)
>   runTest args (_test_dedupeL_unique t)
>   runTest args (_test_dedupeL_delete t)
>   runTest args (_test_dedupeL_involution t)
>   runTest args (_test_dedupeL_eq_unique t)
>   runTest args (_test_dedupeL_prefix t)

And ``main``:

> main_dedupe :: IO ()
> main_dedupe = do
>   _test_dedupe (nil :: ConsList Bool)  20 100
>   _test_dedupe (nil :: ConsList Unary) 20 100
