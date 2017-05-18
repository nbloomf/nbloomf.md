---
title: Elt
author: nbloomf
date: 2017-05-20
tags: arithmetic-made-difficult, literate-haskell
---

> module Elt
>   ( elt, _test_elt, main_elt
>   ) where
> 
> import Booleans
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
> import Filter
> 
> import Prelude (Show, Int, IO, (.))
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define a boolean function, $\elt$, which detects whether or not a given $a$ is an item in a list. As usual we want to define $\elt$ as a fold: should we use a right fold or a left fold? Recall that the tradeoff between the two is that foldl is tail recursive, but foldr does not necessarily have to process the entire list. In this case, $\elt(a,x)$ should be able to return early once it sees an $a$. So lets say $$\elt(a,x) = \foldr{\varepsilon}{\varphi}(x).$$ Now what should $\varepsilon$ and $\varphi$ be? Well, we want
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \elt(a,\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(x) \\
 & = & \varepsilon,
\end{eqnarray*}$$
and if $a = b$ we want
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \elt(a,\cons(b,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(b,x)) \\
 & = & \varphi(b,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(b,\elt(a,x))
\end{eqnarray*}$$
while if $a \neq b$ we want
$$\begin{eqnarray*}
 &   & \elt(a,x) \\
 & = & \elt(a,\cons(b,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(b,x)) \\
 & = & \varphi(b,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(b,\elt(a,x)).
\end{eqnarray*}$$
With this in mind we define $\elt$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \rightarrow A \rightarrow \bool \rightarrow \bool$ by $$\varphi(a)(b,p) = \bif{\beq(a,b)}{\btrue}{p}.$$ Now define $\elt : A \times \lists{A} \rightarrow \bool$ by $$\elt(a,x) = \foldr{\bfalse}{\varphi(a)}(x).$$
</p></div>
</div>

We can translate $\elt$ to Haskell directly as follows:

> elt' :: (List t, Equal a) => a -> t a -> Bool
> elt' a = foldr False (phi a)
>   where
>     phi a b p = if a ==== b then True else p

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\elt(a,\nil) = \bfalse$.
2. $\elt(a,\cons(b,x)) = \bif{\beq(a,b)}{\btrue}{\elt(a,x)}$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \elt(a,\nil) \\
 & = & \foldr{\bfalse}{\varphi(a)}(\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \elt(a,\cons(b,x)) \\
 & = & \foldr{\bfalse}{\varphi(a)}(\cons(b,x)) \\
 & = & \varphi(a)(b,\foldr{\bfalse}{\varphi(a)}(x)) \\
 & = & \varphi(a)(b,\elt(a,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,x)}
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> elt :: (List t, Equal a) => a -> t a -> Bool
> elt a x = case listShape x of
>   Nil      -> False
>   Cons b w -> if a ==== b
>     then True
>     else elt a w

Now $\elt$ interacts with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have $$\elt(a,\cat(x,y)) = \bor(\elt(a,x),\elt(a,y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\cat(x,y)) \\
 & = & \elt(a,\cat(\nil,y)) \\
 & = & \elt(a,y) \\
 & = & \bor(\bfalse,\elt(a,y)) \\
 & = & \bor(\elt(a,\nil),\elt(a,y)) \\
 & = & \bor(\elt(a,x),\elt(a,y))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $y$ some $x$, and let $b \in A$. If $b = a$ we have
$$\begin{eqnarray*}
 &   & \elt(a,\cat(\cons(b,x),y)) \\
 & = & \elt(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,\cat(x,y))} \\
 & = & \btrue \\
 & = & \bor(\btrue,\elt(a,y)) \\
 & = & \bor(\bif{\beq(a,b)}{\btrue}{\elt(a,x)},\elt(a,y)) \\
 & = & \bor(\elt(a,\cons(b,x)),\elt(a,y))
\end{eqnarray*}$$
as claimed. If $b \neq a$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\cat(\cons(b,x),y)) \\
 & = & \elt(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,\cat(x,y))} \\
 & = & \elt(a,\cat(x,y)) \\
 & = & \bor(\elt(a,x),\elt(a,y)) \\
 & = & \bor(\bif{\beq(a,b)}{\btrue}{\elt(a,x)},\elt(a,y)) \\'
 & = & \bor(\elt(a,\cons(b,x)),\elt(a,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And with $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\elt(a,x) = \elt(a,\rev(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\rev(x)) \\
 & = & \elt(a,\rev(\nil)) \\
 & = & \elt(a,\nil) \\
 & = & \elt(a,x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \elt(a,\rev(\cons(b,x))) \\
 & = & \elt(a,\snoc(b,\rev(x))) \\
 & = & \elt(a,\cat(\snoc(b,\rev(x)),\nil)) \\
 & = & \elt(a,\cat(\rev(x),\cons(b,\nil))) \\
 & = & \bor(\elt(a,\rev(x)),\elt(a,\cons(b,\nil))) \\
 & = & \bor(\elt(a,x),\elt(a,\cons(b,\nil))) \\
 & = & \bor(\elt(a,\cons(b,\nil)),\elt(a,x)) \\
 & = & \elt(a,\cat(\cons(b,\nil),x)) \\
 & = & \elt(a,\cons(b,\cat(\nil,x))) \\
 & = & \elt(a,\cons(b,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\elt$ interacts with $\map(f)$ when $f$ is injective:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets and suppose $f : A \rightarrow B$ is injective. Then for all $a \in A$ and $x \in \lists{A}$ we have $$\elt(a,x) = \elt(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \elt(a,\nil) \\
 & = & \bfalse \\
 & = & \elt(f(a),\nil) \\
 & = & \elt(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $x$ and let $b \in A$. Then we have
$$\begin{eqnarray*}
 &   & \elt(a,\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,x)} \\
 & = & \bif{\beq(f(a),f(b))}{\btrue}{\elt(f(a),\map(f)(x))} \\
 & = & \elt(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \elt(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

As a special case, the items in $\tails(x)$ and $\inits(x)$ are precisely the suffixes and prefixes of $x$, respectively.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. We have the following.

1. $\elt(y,\tails(x)) = \suffix(y,x)$.
2. $\elt(y,\inits(x)) = \prefix(y,x)$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we consider two cases. If $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \elt(y,\tails(x)) \\
 & = & \elt(\nil,\tails(\nil)) \\
 & = & \elt(\nil,\cons(\nil,\nil)) \\
 & = & \bif{\beq(\nil,\nil)}{\btrue}{\elt(\nil,\nil)} \\
 & = & \btrue \\
 & = & \prefix(\nil,\nil) \\
 & = & \prefix(\rev(\nil),\rev(\nil)) \\
 & = & \suffix(\nil,\nil) \\
 & = & \suffix(y,x)
\end{eqnarray*}$$
as claimed. Suppose $y \neq \nil$; then we have $y = \snoc(b,u)$ for some $b \in A$ and $u \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \elt(y,\tails(x)) \\
 & = & \elt(y,\tails(\nil)) \\
 & = & \elt(y,\cons(\nil,\nil)) \\
 & = & \bif{\beq(y,\nil)}{\btrue}{\elt(y,\nil)} \\
 & = & \elt(y,\nil) \\
 & = & \bfalse \\
 & = & \suffix(\snoc(b,u),\nil) \\
 & = & \suffix(y,x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $y$ for some $x$ and let $a \in A$. Again we consider two possibilities for $y$. If $y = \cons(a,x)$, we have
$$\begin{eqnarray*}
 &   & \elt(y,\tails(\cons(a,x))) \\
 & = & \elt(y,\cons(\cons(a,x),\tails(x))) \\
 & = & \bif{\beq(y,\cons(a,x)}{\btrue}{\elt(y,\tails(x)} \\
 & = & \btrue \\
 & = & \suffix(\cons(a,x),\cons(a,x)) \\
 & = & \suffix(y,\cons(a,x))
\end{eqnarray*}$$
as claimed. Suppose $y \neq \cons(a,x)$. Now
$$\begin{eqnarray*}
 &   & \elt(y,\tails(\cons(a,x))) \\
 & = & \elt(y,\cons(\cons(a,x),\tails(x))) \\
 & = & \bif{\beq(y,\cons(a,x))}{\btrue}{\elt(y,\tails(x)} \\
 & = & \elt(y,tails(x)) \\
 & = & \suffix(y,x) \\
 & = & \suffix(y,\cons(a,x))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \elt(y,\inits(x)) \\
 & = & \elt(y,\rev(\map(\rev)(\tails(\rev(x))))) \\
 & = & \elt(y,\map(\rev)(\tails(\rev(x)))) \\
 & = & \elt(\rev(y),\map(\rev)(\map(\rev)(\tails(\rev(x))))) \\
 & = & \elt(\rev(y),\map(\rev \circ \rev)(\tails(\rev(x)))) \\
 & = & \elt(\rev(y),\tails(\rev(x))) \\
 & = & \suffix(\rev(y),\rev(x)) \\
 & = & \prefix(y,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

As another special case:

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x \in \lists{A}$. Then $$\elt(a,\filter(\bnot(\beq(a,-)),x)) = \bfalse.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\filter(\bnot(\beq(a,-)),\nil)) \\
 & = & \elt(a,\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for $x$ and let $b \in A$. We have two possibilities. If $b = a$ (that is, $\bnot(\beq(a,b)) = \bfalse$), we have
$$\begin{eqnarray*}
 &   & \elt(a,\filter(\bnot(\beq(a,-)),\cons(b,x))) \\
 & = & \elt(a,\filter(\bnot(\beq(a,-)),x)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed. If $b \neq a$ (that is, $\bnot(\beq(a,b)) = \btrue$), we have
$$\begin{eqnarray*}
 &   & \elt(a,\filter(\bnot(\beq(a,-)),\cons(b,x))) \\
 & = & \elt(a,\cons(b,\filter(\bnot(\beq(a,-),x))) \\
 & = & \filter(\bnot(\beq(a,-)),x) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x

Here are our property tests for $\elt$:

> -- elt'(a,x) == elt(a,x)
> _test_elt_alt :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_elt_alt _ a x =
>     (elt a x) ==== (elt' a x)
> 
> 
> -- elt(a,nil) == false
> _test_elt_nil :: (List t, Equal a)
>   => t a -> a -> Bool
> _test_elt_nil x a =
>   let
>     nil' = nil `withTypeOf` x
>   in
>     (elt a nil') ==== False
> 
> 
> -- elt(a,cat(x,y)) == or(elt(a,x),elt(a,y))
> _test_elt_cat :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> ListOf t a -> Bool
> _test_elt_cat _ a x y =
>     (elt a (cat x y)) ==== ((elt a x) ||| (elt a y))
> 
> 
> -- elt(a,x) == elt(a,rev(x))
> _test_elt_rev :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_elt_rev _ a x =
>     (elt a x) ==== (elt a (rev x))
> 
> 
> -- elt(y,tails(x)) == suffix(y,x)
> _test_elt_tails :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_elt_tails _ x y =
>     (elt y (tails x)) ==== (suffix y x)
> 
> 
> -- elt(y,inits(x)) == prefix(y,x)
> _test_elt_inits :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_elt_inits _ x y =
>     (elt y (inits x)) ==== (prefix y x)
> 
> 
> -- elt(a,filter(eq(a,-),x)) == false
> _test_elt_filter_eq :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_elt_filter_eq _ a x =
>     (elt a (filter (not . eq a) x)) ==== False

And the suite:

> -- run all tests for elt
> _test_elt ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a
>   , List t
>   ) => t a -> Int -> Int -> IO ()
> _test_elt t maxSize numCases = do
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_elt_alt t)
>   runTest args (_test_elt_nil t)
>   runTest args (_test_elt_cat t)
>   runTest args (_test_elt_rev t)
>   runTest args (_test_elt_tails t)
>   runTest args (_test_elt_inits t)
>   runTest args (_test_elt_filter_eq t)

And ``main``:

> main_elt :: IO ()
> main_elt = do
>   _test_elt (nil :: ConsList Bool) 20 100
>   _test_elt (nil :: ConsList Unary) 20 100
