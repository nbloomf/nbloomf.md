---
title: Range
author: nbloomf
date: 2017-05-05
tags: arithmetic-made-difficult, literate-haskell
---

> module Range
>   ( range, _test_range, main_range
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length, head, tail, map)
> 
> import NaturalNumbers
>
> import Lists
> import Reverse
> import Cat
> import Length
> import At
> import Map
> import UnfoldN
> 
> import Test.QuickCheck



<div class="result">
<div class="defn"><p>
Define $f : \nats \rightarrow \ast + \nats \times \nats$ by $$f(k) = (\next(k),k).$$ We then define $\range : \nats \times \nats \rightarrow \lists{\nats}$ by $$\range(a,b) = \unfoldN(f,b,a).$$

In Haskell:

> range :: (ListOf t, Natural n) => n -> n -> t n
> range a b = unfoldN f b a
>   where f k = Just (next k, k)

</p></div>
</div>

In this post we let $\Theta = \bailrec{\varphi}{\beta(f)}{\psi}{\omega(f)}$ as in the definition of $\unfoldN$.

Special cases:

<div class="result">
<div class="thm"><p>
For all $a \in \nats$ we have the following.

1. $\range(a,\zero) = \nil$.
2. $\range(a,\next(\zero)) = \cons(a,\nil)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \range(a,\zero) \\
 & = & \unfoldN(f,\zero,a) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \range(a,\next(\zero)) \\
 & = & \unfoldN(f,\next(\zero),a) \\
 & = & \Theta(\next(\zero),(a,\nil)) \\
 & = & \Theta(\zero,(\next(a),\cons(a,\nil))) \\
 & = & \rev(\cons(a,\nil)) \\
 & = & \cons(a,\nil)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
For all $a,b \in \nats$ we have the following.

1. $\range(a,\next(b)) = \cons(a,\range(\next(a),b))$.
2. $\range(a,\next(b)) = \snoc(\nplus(a,b),\range(a,b))$.
3. $\length(\range(a,b)) = b$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \range(a,\next(b)) \\
 & = & \unfoldN(f,\next(b),a) \\
 & = & \Theta(\next(b),(a,\nil)) \\
 & = & \Theta(b,(\next(a),\cons(a,\nil))) \\
 & = & \cat(\rev(\cons(a,\nil)),\unfoldN(f,b,\next(a))) \\
 & = & \cat(\cons(a,\nil),\range(\next(a),b)) \\
 & = & \cons(a,\cat(\nil,\range(\next(a),b))) \\
 & = & \cons(a,\range(\next(a),b)
\end{eqnarray*}$$
as claimed.
2. We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(a,\next(b)) \\
 & = & \range(a,\next(\zero)) \\
 & = & \cons(a,\nil) \\
 & = & \snoc(a,\nil) \\
 & = & \snoc(\nplus(a,\zero),\range(a,\zero)) \\
 & = & \snoc(\nplus(a,b),\range(a,b)) \\
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $b$. Then we have
$$\begin{eqnarray*}
 &   & \range(a,\next(\next(b)) \\
 & = & \cons(a,\range(\next(a),\next(b))) \\
 & = & \cons(a,\snoc(\nplus(\next(a),b),\range(\next(a),b))) \\
 & = & \snoc(\nplus(\next(a),b),\cons(a,\range(\next(a),b))) \\
 & = & \snoc(\nplus(a,\next(b)),\range(a,\next(b)))
\end{eqnarray*}$$
as needed.
3. We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\range(a,b)) \\
 & = & \length(\range(a,\zero)) \\
 & = & \length(\nil) \\
 & = & \zero \\
 & = & b
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $b$. Now
$$\begin{eqnarray*}
 &   & \length(\range(a,\next(b)) \\
 & = & \length(\cons(a,\range(\next(a),b))) \\
 & = & \next(\length(\range(\next(a),b)) \\
 & = & \next(b)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
If $a,b,c \in \nats$, we have $$\range(a,\nplus(b,c)) = \cat(\range(a,b),\range(\nplus(a,b),c).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $c$. For the base case $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(a,\nplus(b,c)) \\
 & = & \range(a,\nplus(b,\zero)) \\
 & = & \range(a,b) \\
 & = & \cat(\range(a,b),\nil) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),\zero)) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),c))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $c$. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \range(a,\nplus(b,\next(c))) \\
 & = & \range(a,\next(\nplus(b,c))) \\
 & = & \snoc(\nplus(a,\nplus(b,c)),\range(a,\nplus(b,c))) \\
 & = & \snoc(\nplus(a,\nplus(b,c)),\cat(\range(a,b),\range(\nplus(a,b),c))) \\
 & = & \snoc(\nplus(\nplus(a,b),c),\cat(\range(a,b),\range(\nplus(a,b),c))) \\
 & = & \cat(\range(a,b),\snoc(\nplus(\nplus(a,b),c),\range(\nplus(a,b),c))) \\
 & = & \cat(\range(a,b),\range(\nplus(a,b),\next(c)))
\end{eqnarray*}$$
as needed.
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

A utility for type fixing:

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x

Here are our property tests for $\range$.

> -- range(a,next(b)) == cons(a,range(next(a),b))
> _test_range_cons :: (ListOf t, Natural n)
>   => t n -> n -> n -> Bool
> _test_range_cons t a b =
>   let
>     x = (range a (next b)) `withTypeOf` t
>     y = (cons a (range (next a) b))
>   in
>     x `listEq` y

And the suite:

> -- run all tests for range
> _test_range :: (ListOf t, Arbitrary (t n), Show (t n), Natural n, Arbitrary n, Show n)
>   => t n -> n -> Int -> Int -> IO ()
> _test_range t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_range_cons t n)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_range :: IO ()
> main_range = _test_range (nil :: List Nat) (zero :: Nat) 20 100
