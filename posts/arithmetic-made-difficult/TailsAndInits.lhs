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
> import Prelude hiding (foldr, foldl', foldl, map, zip, all, any, tail, length)
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
> 
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll construct the lists of all suffixes ($\tails$) and prefixes ($\inits$) of a list. Starting with $\tails$: this function should have a signature like $$\lists{A} \rightarrow \lists{\lists{A}}.$$ Here's how I did it: we have (almost) one suffix for each item in the list -- the suffix starting at that item -- plus the empty suffix. This suggests we can define $\tails$ as a fold. The hitch is in the return type; fold prefers to decompose a list, while it appears that $\tails$ is building a list up. As usual, the way to handle this is by folding a list of *functions*. The only way I can see to do this is by defining $\tails$ as $$\tails(x) = \foldr{\varepsilon}{\varphi}(x)(x)$$ for some appropriate $\varepsilon$ and $\varphi$. Unpacking this using the behavior we want, I get the following definition.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\varepsilon(w) = \cons(w,\nil)$$ and define $\varphi : A \times \lists{\lists{A}}^{\lists{A}} \rightarrow \lists{\lists{A}}^{\lists{A}}$ by $$\varphi(a,f)(w) = \cons(w,f(\tail(w))).$$ Now define $\tails : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\tails(x) = \foldr{\varepsilon}{\varphi}(x)(x).$$
</p></div>
</div>

We can translate $\tails$ to Haskell directly as follows:

> tails' :: (ListOf t) => t a -> t (t a)
> tails' x = foldr epsilon phi x x
>   where
>     epsilon w = cons w nil
>     phi _ f w = cons w (f (tail w))

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$ we have the following.

1. $\tails(\nil) = \cons(\nil,\nil)$.
2. $\tails(\cons(a,x)) = \cons(\cons(a,x),\tails(x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \tails(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(\nil) \\
 & = & \varepsilon(\nil) \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tails(\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(a,x)) \\
 & = & \cons(\cons(a,x),\foldr{\varepsilon}{\varphi}(x)(\tail(\cons(a,x)))) \\
 & = & \cons(\cons(a,x),\foldr{\varepsilon}{\varphi}(x)(x)) \\
 & = & \cons(\cons(a,x),\tails(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> tails :: (ListOf t) => t a -> t (t a)
> tails x = case listShape x of
>   Nil      -> cons nil nil
>   Cons a w -> cons (cons a w) (tails w)

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$ we have $$\tails(\map(f)(x)) = \map(\map(f))(\tails(x)).$$
</p></div>

$\tails$ interacts with $\map$:

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\nil)) \\
 & = & \tails(\nil) \\
 & = & \nil \\
 & = & \map(\map(f))(\nil) \\
 & = & \map(\map(f))(\tails(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\cons(a,x))) \\
 & = & \tails(\cons(f(a),\map(f)(x))) \\
 & = & \cons(\cons(f(a),\map(f)(x)),\tails(\map(f)(x))) \\
 & = & \cons(\cons(f(a),\map(f)(x)),\map(\map(f))(\tails(x))) \\
 & = & \cons(\map(f)(\cons(a,x)),\map(\map(f))(\tails(x))) \\
 & = & \map(\map(f))(\cons(\cons(a,x),\tails(x))) \\
 & = & \map(\map(f))(\tails(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\tails$ interacts with $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\tails(x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\tails(\nil)) \\
 & = & \length(\cons(\nil,\nil)) \\
 & = & \next(\zero) \\
 & = & \next(\length(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \length(\tails(\cons(a,x))) \\
 & = & \length(\cons(\cons(a,x),\tails(x))) \\
 & = & \next(\length(\tails(x))) \\
 & = & \next(\next(\length(x)) \\
 & = & \next(\length(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Next we'll define $\inits$ in terms of $\tails$.

> inits :: (ListOf t) => t a -> t (t a)
> inits x = map rev (tails (rev x))

$\inits$ interacts with $\map$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\inits(\map(f)(x)) = \map(\map(f))(\inits(x)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \inits(\map(f)(x)) \\
 & = & \map(\rev)(\tails(\rev(\map(f)(x)))) \\
 & = & \map(\rev)(\tails(\map(f)(\rev(x)))) \\
 & = & \map(\rev)(\map(\map(f))(\tails(\rev(x)))) \\
 & = & \map(\rev \circ \map(f))(\tails(\rev(x))) \\
 & = & \map(\map(f) \circ \rev)(\tails(\rev(x))) \\
 & = & \map(\map(f))(\map(\rev)(\tails(\rev(x)))) \\
 & = & \map(\map(f))(\inits(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\length(\inits(x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
Note that
$$begin{eqnarray*}
 &   & \length(\inits(x)) \\
 & = & \length(\map(\rev)(\tails(\rev(x)))) \\
 & = & \length(\tails(\rev(x))) \\
 & = & \next(\length(\rev(x))) \\
 & = & \next(\length(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\tails$ and $\inits$:

> -- tails(x) == tails'(x)
> _test_tails_alt :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_tails_alt _ x =
>   listEqBy listEq (tails x) (tails' x)
> 
> 
> -- tails(map(f)(x)) == map(map(f))(tails(x))
> _test_tails_map :: (ListOf t, Eq a)
>   => t a -> (a -> a) -> t a -> Bool
> _test_tails_map _ f x =
>   listEqBy listEq (tails (map f x)) (map (map f) (tails x))
> 
> 
> -- length(tails(x)) == next(length(x))
> _test_tails_length :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_tails_length _ x =
>   (length (tails x)) == (next (length x))
> 
> 
> -- inits(map(f)(x)) == map(map(f))(inits(x))
> _test_inits_map :: (ListOf t, Eq a)
>   => t a -> (a -> a) -> t a -> Bool
> _test_inits_map _ f x =
>   listEqBy listEq (inits (map f x)) (map (map f) (inits x))
> 
> 
> -- length(inits(x)) == next(length(x))
> _test_inits_length :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_inits_length _ x =
>   (length (inits x)) == (next (length x))

And the suite:

> -- run all tests for tails and inits
> _test_tails_inits :: (ListOf t, Arbitrary a, CoArbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_tails_inits t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_tails_alt t)
>   , quickCheckWith args (_test_tails_map t)
>   , quickCheckWith args (_test_tails_length t)
> 
>   , quickCheckWith args (_test_inits_map t)
>   , quickCheckWith args (_test_inits_length t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_tails_inits :: IO ()
> main_tails_inits = _test_tails_inits (nil :: List Bool) 20 100
