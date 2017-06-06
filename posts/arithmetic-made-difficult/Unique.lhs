---
title: Unique
author: nbloomf
date: 2017-05-26
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
> import LessThanOrEqualTo
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
> import Select
> 
> import Prelude (uncurry)
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll introduce a boolean function $\unique$ to detect whether or not a list has any duplicate items. As usual, we'd like to define $\unique$ as a fold. The signature needs to be $$\lists{A} \rightarrow \bool.$$ How can we do this? Intuitively, we might say

1. $\nil$ is unique, and
2. $\cons(a,x)$ is unique if $x$ is unique and $a$ does not appear in $x$.

Note that $\unique$ will need to "have it's cake and eat it too"; that is, when testing $\cons(a,x)$ for uniqueness we have to check that $x$ is unique (eat the cake) *and* check that $a$ does not appear in $x$ (have the cake). We had a similar problem when we defined $\tails$; the solution there was to define $\tails(x)$ as a fold on $x$ that constructs a function which destructs $x$ again. Taking this tack, we will look for suitable $\varepsilon$ and $\varphi$ so that $$\unique(x) = \foldr{\varepsilon}{\varphi}(x)(x)$$ does what we want.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \bool$ by $\varepsilon(x) = \btrue$, and define $\varphi : A \rightarrow \bool^{\lists{A}} \rightarrow \bool^{\lists{A}}$ by $$\varphi(a,f)(w) = \left\{\begin{array}{ll} \btrue & \mathrm{if}\ w = \nil \\ \band(\all(\bnot(\beq(a,-)),u),f(u)) & \mathrm{if}\ w = \cons(a,u) \end{array}\right.$$ Now we define $\unique : \lists{A} \rightarrow \bool$ by $$\unique(x) = \foldr{\varepsilon}{\varphi}(x)(x).$$

In Haskell:

> unique' :: (List t, Equal a) => t a -> Bool
> unique' x = foldr epsilon phi x x
>   where
>     epsilon _ = True
> 
>     phi a f w = case listShape w of
>       Nil      -> True
>       Cons _ u -> and (all (\b -> not (eq a b)) u) (f u)

</p></div>
</div>

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\unique(\nil) = \btrue$.
2. $\unique(\cons(a,x)) = \band(\all(\bnot(\beq(a,-)),x),\unique(x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \unique(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(\nil) \\
 & = & \varepsilon(\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \unique(\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(a,x)) \\
 & = & \band(\all(\not(\beq(a,-)),x),\foldr{\varepsilon}{\varphi}(x)(x)) \\
 & = & \band(\all(\not(\beq(a,-)),x),\unique(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> unique :: (List t, Equal a) => t a -> Bool
> unique x = case listShape x of
>   Nil      -> True
>   Cons a u -> and (all (not . eq a) u) (unique u)

$\unique$ interacts with $\sublist$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$ and $\unique(y) = \btrue$, then $\unique(x) = \btrue$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, suppose $\sublist(x,y) = \btrue$. Then we have $y = \nil$ and $x = \nil$, and thus $\unique(x) = \btrue$. For the inductive step, suppose the implication holds for all $x$ for some $y$ and let $b \in A$. Suppose further that $\unique(\cons(b,y)) = \btrue$ and $\sublist(x,\cons(b,y)) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, then $\unique(x) = \btrue$ as needed. Suppose instead that $x = \cons(a,u)$ for some $a \in A$ and $u \in \lists{A}$. Note first that since $\unique(\cons(b,y)) = \btrue$, we have $$\band(\all(\bnot(\beq(a,-)),x),\unique(y)) = \btrue;$$ in particular, $\unique(y) = \btrue$.  We now consider two possibilities. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(\cons(a,u),y) \\
 & = & \sublist(x,y).
\end{eqnarray*}$$
By the inductive hypothesis we have $\unique(x) = \btrue$ as needed. Suppose instead that $a = b$. Now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y).
\end{eqnarray*}$$
Again by the inductive hypothesis we have $\unique(u) = \btrue$. Since $\sublist(u,y) = \btrue$, we also have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \unique(\cons(b,y)) \\
 & = & \unique(\cons(a,y)) \\
 & = & \band(\all(\bnot(\beq(a,-)),y),\unique(y)) \\
 & = & \all(\bnot(\beq(a,-)),y) \\
 & = & \all(\bnot(\beq(a,-)),u).
\end{eqnarray*}$$
Thus we have
$$\begin{eqnarray*}
 &   & \unique(x) \\
 & = & \unique(\cons(a,u)) \\
 & = & \band(\all(\bnot(\beq(a,-)),u),\unique(u)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\range$s are unique.

<div class="result">
<div class="thm"><p>
Let $a,b \in \nats$. Then $\unique(\range(a,b)) = \btrue$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

If $f$ is injective, $\map(f)$ preserves uniqueness:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $x \in \lists{A}$ and $f : A \rightarrow B$. If $f$ is injective then $\unique(x) = \unique(\map(f)(x))$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \unique(\map(f)(x)) \\
 & = & \unique(\map(f)(\nil)) \\
 & = & \unique(\nil) \\
 & = & \unique(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $f$ for some $x$ and let $a \in A$. Suppose further that $\unique(\cons(a,x)) = \btrue$. Now if $f$ is injective, we have $\beq(f(a),f(-)) = \beq(a,-)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \unique(\map(f)(\cons(a,x))) \\
 & = & \unique(\cons(f(a),\map(f)(x))) \\
 & = & \band(\all(\bnot(\beq(f(a),-)),\map(f)(x)),\unique(\map(f)(x))) \\
 & = & \band(\all(\bnot(\beq(f(a),-)) \circ f,x),\btrue) \\
 & = & \band(\all(\bnot(\beq(f(a),f(-))),x),\btrue) \\
 & = & \band(\all(\bnot(\beq(a,-)),x),\btrue) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\unique$ and $\select$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\unique(x) = \all(\unique(-),\select(\next(\next(\zero)),x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, (@@@)
</p></div>
</div>


Testing
-------

Here are our property tests for $\unique$:

> _test_unique_alt :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_unique_alt _ =
>   testName "unique'(x) == unique(x)" $
>    \x -> (unique x) ==== (unique' x)
> 
> 
> _test_unique_rev :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_unique_rev _ =
>   testName "unique(x) == unique(rev(x))" $
>    \x -> (unique x) ==== (unique (rev x))
> 
> 
> _test_unique_sublist :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_unique_sublist _ =
>   testName "unique(x) & sublist(y,x) ==> unique(y)" $
>    \x y -> if (unique x) &&& (sublist y x)
>      then (unique y) ==== True
>      else True

And the suite:

> -- run all tests for unique
> _test_unique ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_unique t n maxSize numCases = do
>   testLabel ("unique: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_unique_alt t)
>   runTest args (_test_unique_rev t)
>   runTest args (_test_unique_sublist t)

And ``main``:

> main_unique :: IO ()
> main_unique = do
>   _test_unique (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_unique (nil :: ConsList Unary) (zero :: Unary) 20 100
