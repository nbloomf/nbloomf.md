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
Let $A$ be a set, and define $f : A \rightarrow \ast + A \times A$ by $f(x) = (x,x)$. Now define $\repeat : \nats \times A \rightarrow \lists{A}$ by $$\repeat(n,a) = \unfoldN(f,n,a).$$
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
1. Note that
$$\begin{eqnarray*}
 &   & \repeat(\zero,a) \\
 & = & \unfoldN(f,\zero,a) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \repeat(\next(k),a) \\
 & = & \unfoldN(f,\next(k),a) \\
 & = & \cons(a,\unfoldN(f,k,a)) \\
 & = & \cons(a,\repeat(k,a))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> repeat :: (List t, Equal a, Natural n) => n -> a -> t a
> repeat n a = case natShape n of
>   Zero   -> nil
>   Next k -> cons a (repeat k a)

$\repeat$ is kind of boring. I'm not sure if we'll actually need these, but here are some interactions using $\repeat$.

First, $\repeat$ and $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $n \in \nats$ and $a \in A$ we have $$\length(\repeat(n,a)) = n.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \length(\repeat(\zero,a)) \\
 & = & \length(\nil) \\
 & = & \zero
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $n$. Then we have
$$\begin{eqnarray*}
 &   & \length(\repeat(\next(n),a)) \\
 & = & \length(\cons(a,\repeat(n,a))) \\
 & = & \next(\length(\repeat(n,a))) \\
 & = & \next(n)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\repeat$ and $\map$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $n \in \nats$ and $a \in A$, we have $$\map(f)(\repeat(n,a)) = \repeat(n,f(a)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$ we have
$$\begin{eqnarray*}
 &   & \map(f)(\repeat(\zero,a)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \repeat(\zero,f(a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now we have
$$\begin{eqnarray*}
 &   & \map(f)(\repeat(\next(n),a)) \\
 & = & \map(f)(\cons(a,\repeat(n,a))) \\
 & = & \cons(f(a),\map(f)(\repeat(n,a))) \\
 & = & \cons(f(a),\repeat(n,f(a))) \\
 & = & \repeat(\next(n),f(a))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\repeat$ and $\nplus$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $m,n \in \nats$ and $a \in A$, we have $$\repeat(\nplus(m,n),a) = \cat(\repeat(m,a),\repeat(n,a)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $m$. For the base case $m = \zero$, we have
$$\begin{eqnarray*}
 &   & \repeat(\nplus(\zero,n),a) \\
 & = & \repeat(n,a) \\
 & = & \cat(\nil,\repeat(n,a)) \\
 & = & \cat(\repeat(\zero,a),\repeat(n,a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $m$. Now we have
$$\begin{eqnarray*}
 &   & \repeat(\nplus(\next(m),n),a) \\
 & = & \repeat(\next(\nplus(m,n)),a) \\
 & = & \cons(a,\repeat(\nplus(m,n),a)) \\
 & = & \cons(a,\cat(\repeat(m,a),\repeat(n,a))) \\
 & = & \cat(\cons(a,\repeat(m,a)),\repeat(n,a)) \\
 & = & \cat(\repeat(\next(m),a),\repeat(n,a))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally, $\repeat$ and $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $n \in \nats$ and $a \in A$, we have the following.

1. $\snoc(a,\repeat(n,a)) = \repeat(\next(n),a).$$
2. $\rev(\repeat(n,a)) = \repeat(n,a)$.
</p></div>

<div class="proof"><p>
1. We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \snoc(a,\repeat(\zero,a)) \\
 & = & \snoc(a,\nil) \\
 & = & \cons(a,\nil) \\
 & = & \cons(a,\repeat(\zero,a)) \\
 & = & \repeat(\next(\zero),a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now we have
$$\begin{eqnarray*}
 &   & \snoc(a,\repeat(\next(n),a)) \\
 & = & \snoc(a,\cons(a,\repeat(n,a))) \\
 & = & \cons(a,\snoc(a,\repeat(n,a))) \\
 & = & \cons(a,\repeat(\next(n),a)) \\
 & = & \repeat(\next(\next(n)),a)
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \rev(\repeat(\zero,a)) \\
 & = & \rev(\nil) \\
 & = & \nil \\
 & = & \repeat(\zero,a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Then we have
$$\begin{eqnarray*}
 &   & \rev(\repeat(\next(n),a)) \\
 & = & \rev(\cons(a,\repeat(n,a))) \\
 & = & \snoc(a,\rev(\repeat(n,a))) \\
 & = & \snoc(a,\repeat(n,a)) \\
 & = & \repeat(\next(n),a)
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\repeat$:

> _test_repeat_alt :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> a -> Bool)
> _test_repeat_alt t _ =
>  testName "repeat'(n,a) == repeat(n,a)" $
>  \k a -> let
>    rna = repeat k a `withTypeOf` ListOf t
>  in
>    (repeat' k a) ==== rna
> 
> 
> _test_repeat_length :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> a -> Bool)
> _test_repeat_length t _ =
>  testName "length(repeat(n,a)) == n" $
>  \k a -> let
>    rka = repeat k a `withTypeOf` ListOf t
>  in
>    (length rka) ==== k
> 
> 
> _test_repeat_map :: (List t, Equal a, Equal b, Natural n)
>   => t a -> t b -> n -> Test ((a -> b) -> Nat n -> a -> Bool)
> _test_repeat_map t _ _ =
>  testName "map(f)(repeat(n,a)) == repeat(n,f(a))" $
>  \f k a -> let
>    rka = repeat k a `withTypeOf` ListOf t
>  in
>    (repeat k (f a)) ==== (map f rka)
> 
> 
> _test_repeat_plus :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> Nat n -> a -> Bool)
> _test_repeat_plus t _ =
>  testName "repeat(plus(m,n),a)) == cat(repeat(m,a),repeat(n,a))" $
>  \m n a -> let
>    rma = repeat m a `withTypeOf` ListOf t
>  in
>    (repeat (plus m n) a) ==== (cat rma (repeat n a))
> 
> 
> _test_repeat_snoc :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> a -> Bool)
> _test_repeat_snoc t _ =
>  testName "snoc(a,repeat(n,a)) == repeat(next(n),a)" $
>  \n a -> let
>    rna = repeat n a `withTypeOf` ListOf t
>  in
>    (snoc a rna) ==== (repeat (next n) a)
> 
> 
> _test_repeat_rev :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> a -> Bool)
> _test_repeat_rev t _ =
>  testName "rev(repeat(n,a)) == repeat(n,a)" $
>  \n a -> let
>    rna = repeat n a `withTypeOf` ListOf t
>  in
>    (rev rna) ==== rna

And the suite:

> -- run all tests for repeat
> _test_repeat ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName b, Equal b, Show b, Arbitrary b, CoArbitrary b
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Arbitrary n, Show n
>   ) => t a -> t b -> n -> Int -> Int -> IO ()
> _test_repeat t u n maxSize numCases = do
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
>   runTest args (_test_repeat_map t u n)
>   runTest args (_test_repeat_plus t n)
>   runTest args (_test_repeat_snoc t n)
>   runTest args (_test_repeat_rev t n)

And ``main``:

> main_repeat :: IO ()
> main_repeat = do
>   _test_repeat (nil :: ConsList Bool)  (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_repeat (nil :: ConsList Unary) (nil :: ConsList Unary) (zero :: Unary) 20 100
