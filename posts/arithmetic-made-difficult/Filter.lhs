---
title: Filter
author: nbloomf
date: 2017-05-13
tags: arithmetic-made-difficult, literate-haskell
---

> module Filter
>   ( filter, _test_filter, main_filter
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, map, zip, all, any, tail, length, filter)
> 
> import NaturalNumbers
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> 
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll nail down $\filter$, which takes a list and a predicate on the items and "filters out" the items which satisfy the predicate. $\filter$ should have a signature like $$\bool^A \times \lists{A} \rightarrow \lists{A}.$$ As usual, we want to define $\filter$ as a fold; say $$\filter(p,x) = \foldr{\varepsilon}{\varphi}(x).$$ Where on the right hand side of that equation should the $p$ parameter go? Lets think out loud for a moment. On the one hand, we want
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \filter(p,\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil) \\
 & = & \varepsilon.
\end{eqnarray*}$$
On the other hand, we want
$$\begin{eqnarray*}
 &   & \filter(p,\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(a,\filter(p,x)).
\end{eqnarray*}$$
Intuitively, if $p(a)$ is $\btrue$ we want $$\filter(p,\cons(a,x)) = \cons(a,\filter(p,x)),$$ while if $p(a)$ is $\bfalse$ we want $$\filter(p,\cons(a,x)) = \filter(p,x).$$ With this in mind we define $\filter$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : \bool^A \rightarrow A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(p)(a,w) = \left\{ \begin{array}{ll} \cons(a,w) & \mathrm{if}\ p(a) = \btrue \\ w & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$ Now define $$\filter : \bool^A \times \lists{A} \rightarrow \lists{A}$$ by $$\filter(p,x) = \foldr{\nil}{\varphi(p)}(x).$$
</p></div>
</div>

We can translate $\filter$ to Haskell directly as follows:

> filter' :: (ListOf t) => (a -> Bool) -> t a -> t a
> filter' p x = foldr nil (phi p) x
>   where
>     phi q a w = if q a == True
>       then cons a w
>       else w

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a function. Then we have the following.

1. $\filter(p,\nil) = \nil$.
2. $$\filter(p,\cons(a,x)) = \left\{\begin{array}{ll} \cons(a,\filter(p,x)) & \mathrm{if}\ p(a) = \btrue \\ \filter(p,x) & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>

In Haskell:

> filter :: (ListOf t) => (a -> Bool) -> t a -> t a
> filter p x = case listShape x of
>   Nil      -> nil
>   Cons a w -> if p a == True
>     then cons a (filter p w)
>     else filter p w

As we might expect, the items in $\filter(p,x)$ all satisfy $p$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$ we have $$\all(p,\filter(p,x)) = \btrue.$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

$\filter$ interacts with $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$, we have $$\filter(p,\rev(x)) = \rev(\filter(p,x)).$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

And with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x,y \in \lists{A}$ we have $$\filter(p,\cat(x,y)) = \cat(\filter(p,x),\filter(p,y)).$$
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


Testing
-------

Here are our property tests for $\filter$:

> -- filter(p,x) == filter'(p,x)
> _test_filter_alt :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> Bool
> _test_filter_alt _ p x =
>   (filter p x) `listEq` (filter' p x)
> 
> 
> -- all(p,filter(p,x)) == true
> _test_filter_all :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> Bool
> _test_filter_all _ p x =
>   (all p (filter p x)) == True
> 
> 
> -- filter(p,rev(x)) == rev(filter(p,x))
> _test_filter_rev :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> Bool
> _test_filter_rev _ p x =
>   (filter p (rev x)) `listEq` (rev (filter p x))
> 
> 
> -- filter(p,cat(x,y)) == cat(filter(p,x),filter(p,y))
> _test_filter_cat :: (ListOf t, Eq a)
>   => t a -> (a -> Bool) -> t a -> t a -> Bool
> _test_filter_cat _ p x y =
>   (filter p (cat x y)) `listEq` (cat (filter p x) (filter p y))

And the suite:

> -- run all tests for filter
> _test_filter :: (ListOf t, Arbitrary a, CoArbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_filter t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_filter_alt t)
>   , quickCheckWith args (_test_filter_all t)
>   , quickCheckWith args (_test_filter_rev t)
>   , quickCheckWith args (_test_filter_cat t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_filter :: IO ()
> main_filter = _test_filter (nil :: List Bool) 20 100
