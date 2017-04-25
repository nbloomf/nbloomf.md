---
title: At
author: nbloomf
date: 2017-04-28
tags: arithmetic-made-difficult, literate-haskell
---

> module At
>   ( at, _test_at, main_at
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length, head, tail)
> 
> import NaturalNumbers
> import Plus
> import LessThanOrEqualTo
>
> import Lists
> import Reverse
> import Cat
> import Length
> 
> import Test.QuickCheck

In this post we'll investigate $\at$, which extracts the element at an arbitrary position in a list. First, we need $\head$, which extracts the *first* element of a list. To a first approximation $\head$ has a signature like $$\lists{A} \rightarrow A,$$ and certainly we want $\head(\cons(a,x)) = a$. But what about $\head(\nil)$? In this case there is no element to extract. Taking a cue from our definition of $\nminus$, we will make $\head$ return not an $A$, but a $\ast + A$, letting the $\ast$ represent $\head(\nil)$. Now $\head$ can be expressed as a $\foldr{\ast}{\ast}$ as follows.

<div class="result">
<div class="defn"><p>
Define $\varphi : A \times (\ast + A) \rightarrow \ast + A$ by $$\varphi(a,b) = a.$$ Now we define $\head : \lists{A} \rightarrow \ast + A$ by $$\head = \foldr{\ast}{\varphi}.$$

In Haskell:

> head :: (ListOf t) => t a -> Maybe a
> head = foldr Nothing phi
>   where
>     phi a _ = Just a

</p></div>
</div>

Tracing $\head$ we can see that it indeed extracts the first element of a list.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $a \in A$ and $x \in \lists{A}$, we have $$\head(\cons(a,x)) = a.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \head(\cons(a,x)) \\
 & = & \foldr{\ast}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\ast}{\varphi}(x)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

There's a catch here: $\head$ should in principle do a constant amount of work. It needs to deconstruct only the outermost constructor of its argument. But if we're implementing $\foldr{\ast}{\ast}$ using a language which eagerly evaluates function arguments, it will happily march down the list all the way to the end. Haskell is lazy, so this won't be a problem for us, but it's worth mentioning. Maybe we need a new recursion operator!

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $a \in A$ and $x \in \lists{A}$ with $x \neq \nil$, we have $$\head(\snoc(a,x)) = \head(x).$$
</p></div>

<div class="proof"><p>
If $x \neq \nil$, we have $x = \cons(b,y)$ for some $b \in A$ and $y \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \head(\snoc(a,x)) \\
 & = & \head(\snoc(a,\cons(b,y))) \\
 & = & \head(\cons(b,\snoc(a,y))) \\
 & = & b \\
 & = & \head(\cons(b,y)) \\
 & = & \head(x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

With $\head$ in hand, we can extract arbitrary elements from a list as follows.

<div class="result">
<div class="defn"><p>
Define $\varphi : \lists{A} \rightarrow \ast + A$ by $$\varphi(a) = \ast,$$ $\beta : \nats \times \lists{A} \rightarrow \bool$ by $$\beta(k,x) = \iszero(k) \bor \isnil(x),$$ $\psi : \nats \times \lists{A} \rightarrow \ast + A$ by $$\psi(k,x) = \head(x),$$ and $\omega : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\omega(k,x) = \tail(x).$$ We then define $\at : \lists{A} \times \nats \rightarrow \ast + A$ by $$\at(x,k) = \bailrec{\varphi}{\beta}{\psi}{\omega}(k,x).$$

In Haskell:

> at :: (Natural n, ListOf t) => t a -> n -> Maybe a
> at x k = bailoutRec phi beta psi omega k x
>   where
>     phi   _   = Nothing
>     beta  k x = isZero k || isNil x
>     psi   _ x = head x
>     omega _ x = tail x

</p></div>
</div>

For the remainder of this post, we let $\Theta$ denote $\bailrec{\varphi}{\beta}{\psi}{\omega}$ as in this definition. First lets trace some special cases.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $a,b \in A$, $x \in \lists{A}$, and $k \in \nats$.

1. $\at(\nil,k) = \ast$.
2. $\at(\cons(a,x),\next(\zero)) = a$.
3. $\at(\cons(a,\cons(b,x)),\next(\next(\zero))) = b$.
</p></div>

<div class="proof"><p>
1. We consider two cases: $k = \zero$ and $k \neq \zero$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\zero) \\
 & = & \Theta(\zero,\nil) \\
 & = & \varphi(\nil) \\
 & = & \ast
\end{eqnarray*}$$
as claimed. If $k = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\next(m)) \\
 & = & \Theta(\next(m),\nil) \\
 & = & \psi(m,\nil) \\
 & = & \head(\nil) \\
 & = & \ast
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\next(\zero)) \\
 & = & \Theta(\next(\zero),\cons(a,x)) \\
 & = & \psi(\zero,\cons(a,x)) \\
 & = & \head(\cons(a,x)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),\next(\next(\zero))) \\
 & = & \Theta(\next(\next(\zero)),\cons(a,\cons(b,x))) \\
 & = & \Theta(\next(\zero),\omega(\next(\zero),\cons(a,\cons(b,x)))) \\
 & = & \Theta(\next(\zero),\tail(\cons(a,\cons(b,x)))) \\
 & = & \Theta(\next(\zero),\cons(b,x)) \\
 & = & \at(\cons(b,x),\next(\zero)) \\
 & = & b
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

More generally:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have $$\at(\cons(a,x),\next(\next(k))) = \at(x,\next(k)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\next(\next(k))) \\
 & = & \Theta(\next(\next(k)),\cons(a,x)) \\
 & = & \Theta(\next(k),\omega(\next(k),\cons(a,x))) \\
 & = & \Theta(\next(k),\tail(\cons(a,x))) \\
 & = & \Theta(\next(k),x) \\
 & = & \at(x,\next(k))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We also have:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and let $z \in \lists{A}$. Then $$\at(z,\length(z)) = \head(\rev(z)).$$
</p></div>

<div class="proof"><p>
We consider two cases: either $z = \nil$ or $z = \cons(a,x)$ for some $a \in A$ and $x \in \lists{A}$. If $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\length(\nil)) \\
 & = & \at(\nil,\zero) \\
 & = & \ast \\
 & = & \head(\nil)
\end{eqnarray*}$$
as claimed.

Suppose instead that $z = \cons(a,x)$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \at(z,\length(z)) \\
 & = & \at(\cons(a,\nil),\length(\cons(a,\nil))) \\
 & = & \at(\cons(a,\nil),\next(\zero)) \\
 & = & a \\
 & = & \head(\cons(a,\nil)) \\
 & = & \head(\rev(\cons(a,\nil))) \\
 & = & \head(\rev(z))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $b \in A$. Now we have
$$\begin{eqnarray*}
 &   & \at(z,\length(z)) \\
 & = & \at(\cons(a,\cons(b,x)),\length(\cons(a,\cons(b,x)))) \\
 & = & \at(\cons(a,\cons(b,x)),\next(\next(\length(x)))) \\
 & = & \at(\cons(b,x),\next(\length(x))) \\
 & = & \at(\cons(b,x),\length(\cons(b,x))) \\
 & = & \head(\rev(\cons(b,x))) \\
 & = & \head(\snoc(a,\rev(\cons(b,x)))) \\
 & = & \head(\rev(\cons(a,\cons(b,x)))) \\
 & = & \head(\rev(z))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

We can characterize the $k$ such that $\at(x,k) = \ast$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$ we have the following.

1. If $\nleq(\length(x),k)$, then $\at(x,\next(k)) = \ast$.
2. If $\nleq(\next(\zero),k)$ and $\nleq(k,\length(x))$ then $\at(x,k) \neq \ast$.
</p></div>

<div class="proof"><p>
1. We proceed by induction on $k$. For the base case $k = \zero$, suppose $\nleq(\length(x),\zero)$. Then we have $\length(x) = \zero$, so that $x = \nil$. Now $\at(\nil,\next(\zero)) = \ast$ as claimed. For the inductive step, suppose the implication holds for all $x \in \lists{A}$ for some $k \in \nats$, and suppose further that $x \in \lists{A}$ such that $\nleq(\length(x),\next(k))$. We consider two cases for $x$: either $x = \nil$ or $x = \cons(a,y)$ for some $y$. If $x = \nil$ we have $\at(\nil,\next(k)) = \ast$ as claimed. If $x = \cons(a,y)$, we have $\length(x) = \next(\length(y))$, so that $\nleq(\length(y),k)$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(\next(k))) \\
 & = & \at(\cons(a,y),\next(\next(k))) \\
 & = & \at(y,\next(k)) \\
 & = & \ast
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $k$. For the base case $k = \zero$, note that $\nleq(\next(\zero),k) = \bfalse$, so the implication holds vacuously. For the inductive step, suppose the implication holds for all $x \in \lists{A}$ for some $k \in \nats$. Let $x \in \lists{A}$, and suppose further that $\nleq(\next(\zero),\next(k))$ and $\nleq(\next(k),\length(x))$. Note that $x \neq \nil$; say $x = \cons(a,y)$. We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(k)) \\
 & = & \at(\cons(a,y),\next(\zero)) \\
 & = & a \\
 & \neq & \ast
\end{eqnarray*}$$
as needed. If $k \neq \zero$, we have $k = \next(m)$ for some $m \in \nats$. Note that $\nleq(\next(\zero),k)$ and $\nleq(k,\length(y))$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(k)) \\
 & = & \at(\cons(a,y),\next(\next(m))) \\
 & = & \at(y,\next(m)) \\
 & = & \at(y,k) \\
 & \neq & \ast
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ and $k \in \nats$, we have $$\at(\cat(x,y),k) = \left\{ \begin{array}{ll} \at(x,k) & \mathrm{if}\ \leq(k,\length(x)) \\ \at(y,\next(\nminus(k,\length(x)))) & \mathrm{if}\ \leq(\next(\length(x)),k). \end{array} \right.$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Testing
-------

A utility for type fixing:

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x

Here are our property tests for $\at$.

> -- at(nil,k) == *
> _test_at_nil :: (ListOf t, Eq a, Natural n)
>   => t a -> n -> n -> Bool
> _test_at_nil z _ m =
>   let nil' = nil `withTypeOf` z in
>   (at nil' m) == Nothing
> 
> 
> -- at(cons(a,nil),next(0)) == *
> _test_at_single :: (ListOf t, Eq a, Natural n)
>   => t a -> n -> a -> Bool
> _test_at_single z k a =
>   let
>     nil'  = nil  `withTypeOf` z
>     zero' = zero `withTypeOf` k
>   in
>     (at (cons a nil') (next zero')) == Just a
> 
> 
> -- at(cons(a,cons(b,nil)),next(next(0))) == *
> _test_at_double :: (ListOf t, Eq a, Natural n)
>   => t a -> n -> a -> a -> Bool
> _test_at_double z k a b =
>   let
>     nil'  = nil  `withTypeOf` z
>     zero' = zero `withTypeOf` k
>   in
>     (at (cons a (cons b nil')) (next (next zero'))) == Just b
> 
> 
> -- at(cons(a,x),next(next(k))) == at(x,next(k))
> _test_at_next_next_cons :: (ListOf t, Eq a, Natural n)
>   => t a -> n -> t a -> a -> n -> Bool
> _test_at_next_next_cons z _ x a k =
>   let
>     nil'  = nil  `withTypeOf` z
>   in
>     (at (cons a x) (next (next k))) == (at x (next k))
> 
> 
> -- at(x,length(x)) == head(rev(x))
> _test_at_length_rev :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_at_length_rev z x =
>   (at x (length x)) == (head (rev x))
> 
> 
> -- leq(length(x),k) ==> at(x,next(k)) == *
> -- leq(next(0),k) && leq(k,length(x)) ==> at(x,next(k)) /= *
> _test_at_range :: (ListOf t, Eq a)
>   => t a -> t a -> Nat -> Bool
> _test_at_range _ x n =
>   if n /= zero && leq n (length x)
>     then case at x n of
>       Just _  -> True
>       Nothing -> False
>     else (at x n) == Nothing

And the suite:

> -- run all tests for at
> _test_at :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a), Natural n, Arbitrary n, Show n)
>   => t a -> n -> Int -> Int -> IO ()
> _test_at t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_at_nil t n)
>   , quickCheckWith args (_test_at_single t n)
>   , quickCheckWith args (_test_at_double t n)
>   , quickCheckWith args (_test_at_next_next_cons t n)
>   , quickCheckWith args (_test_at_length_rev t)
>   , quickCheckWith args (_test_at_range t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_at :: IO ()
> main_at = _test_at (nil :: List Bool) (zero :: Nat) 20 100
