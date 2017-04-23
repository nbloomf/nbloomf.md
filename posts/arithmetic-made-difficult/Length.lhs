---
title: Length
author: nbloomf
date: 2017-04-26
tags: arithmetic-made-difficult, literate-haskell
---

> module Length
>   ( length, _test_length, main_length
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length)
> 
> import NaturalNumbers
> import Plus
>
> import Lists
> import Reverse
> import Cat
> 
> import Test.QuickCheck

Today we'll measure the sizes of lists with $\length$. Intuitively this function should "count" the "number" of "items" in a list. Thinking recuresively, it is reasonable to want the length of $\nil$ to be zero, and the length of $\cons(a,x)$ to be one more than the length of $x$. $\foldr{\ast}{\ast}$ was made for situations like this. But wait! Remember that $\foldr{\ast}{\ast}$ is not tail recursive, so on large lists it may have problems. But $\foldl{\ast}{\ast}$ is tail recursive, and is interchangeable with $\foldr{\ast}{\ast}$ *as long as* whatever we're doing to the list doesn't care what *order* the items come in. And it seems reasonable to say that the length of a list is not dependent on the order of its items. With this in mind we define $\length$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times \nats \rightarrow \nats$ by $\varphi(a,k) = \next(k)$, and define $\length : \lists{A} \rightarrow \nats$ by $$\length(x) = \foldl{\zero}{\varphi}(x).$$

In Haskell:

> length :: (ListOf t) => t a -> Nat
> length = foldl zero phi
>   where
>     phi _ k = next k

</p></div>
</div>

We let $\varphi$ be as in this definition for the remainder of this post. Now a lemma:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $a,b \in A$, $k \in \nats$, and $x \in \lists{A}$, we have the following.

1. $\foldl{k}{\varphi}(\cons(a,x)) = \foldl{k}{\varphi}(\cons(b,x))$.
2. $\foldl{k}{\varphi}(\cons(a,x)) = \foldl{k}{\varphi}(\snoc(a,x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \foldl{k}{\varphi}(\cons(a,x)) \\
 & = & \foldr{k}{\varphi}(\rev(\cons(a,x))) \\
 & = & \foldr{k}{\varphi}(\snoc(a,\rev(x))) \\
 & = & \foldr{\varphi(a,k)}{\varphi}(\rev(x)) \\
 & = & \foldr{\next(k)}{\varphi}(\rev(x)) \\
 & = & \foldr{\varphi(b,k)}{\varphi}(\rev(x)) \\
 & = & \foldr{k}{\varphi}(\snoc(b,\rev(x))) \\
 & = & \foldr{k}{\varphi}(\rev(\cons(b,x))) \\
 &   & \foldl{k}{\varphi}(\cons(b,x)) \\
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldl{k}{\varphi}(\cons(a,\nil)) \\
 & = & \foldr{k}{\varphi}(\rev(\cons(a,\nil))) \\
 & = & \foldr{k}{\varphi}(\cons(a,\nil)) \\
 & = & \foldr{k}{\varphi}(\cons(a,\rev(\nil))) \\
 & = & \foldr{k}{\varphi}(\rev(\snoc(a,\nil))) \\
 & = & \foldl{k}{\varphi}(\snoc(a,\nil)) \\
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the result holds for some $x \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \foldl{k}{\varphi}(\snoc(a,\cons(b,x))) \\
 & = & \foldl{k}{\varphi}(\cons(b,\snoc(a,x))) \\
 & = & \foldr{k}{\varphi}(\rev(\cons(b,\snoc(a,x)))) \\
 & = & \foldr{k}{\varphi}(\snoc(b,\rev(\snoc(a,x)))) \\
 & = & \foldr{\varphi(b,k)}{\varphi}(\rev(\snoc(a,x))) \\
 & = & \foldl{\varphi(b,k)}{\varphi}(\snoc(a,x)) \\
 & = & \foldl{\next(k)}{\varphi}(\cons(a,x)) \\
 & = & \foldl{\varphi(a,k)}{\varphi}(\cons(b,x)) \\
 & = & \foldr{\varphi(a,k)}{\varphi}(\rev(\cons(b,x))) \\
 & = & \foldr{k}{\varphi}(\snoc(a,\rev(\cons(b,x)))) \\
 & = & \foldr{k}{\varphi}(\rev(\cons(a,\cons(b,x)))) \\
 & = & \foldl{k}{\varphi}(\cons(a,\cons(b,x))) \\
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In particular:

<div class="result">
<div class="corollary"><p>
For all $a \in A$ and $x \in \lists{A}$:

1. $\length(\cons(a,x)) = \length(\cons(b,x))$.
2. $\length(\cons(a,x)) = \length(\snoc(a,x))$.
</p></div>
</div>

Although $\length$ is defined in terms of $\foldl{\ast}{\ast}$, it has a $\foldr{\ast}{\ast}$-based interpretation as well:

<div class="result">
<div class="thm"><p>
With $\varphi$ as in the definition of $\length$, we have $$\length(x) = \foldr{\zero}{\varphi}.$$ In particuar, $$\length(\cons(a,x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \length(\nil) \\
 & = & \foldl{\zero}{\varphi}(\nil) \\
 & = & \foldr{\zero}{\varphi}(\rev(\nil)) \\
 & = & \foldr{\zero}{\varphi}(\nil)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\cons(a,x)) \\
 & = & \length(\snoc(a,x)) \\
 & = & \foldl{\zero}{\varphi}(\snoc(a,x)) \\
 & = & \foldr{\zero}{\varphi}(\rev(\snoc(a,x))) \\
 & = & \foldr{\zero}{\varphi}(\cons(a,\rev(x))) \\
 & = & \next(\foldr{\zero}{\varphi}(\rev(x))) \\
 & = & \next(\foldl{\zero}{\varphi}(x)) \\
 & = & \next(\length(x)) \\
 & = & \next(\foldl{\zero}{\varphi}(x))
 & = & \varphi(a,\foldr{\zero}{\varphi}(x)) \\
 & = & \foldr{\zero}{\varphi}(\cons(a,x))
\end{eqnarray*}$$
as needed.

Now note that
$$\begin{eqnarray*}
 &   & \length(\cons(a,x)) \\
 & = & \foldr{\zero}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\zero}{\varphi}(x)) \\
 & = & \varphi(a,\length(x)) \\
 & = & \next(\length(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Special cases.

<div class="result">
<div class="thm"><p>
For all $a,b \in A$, we have:

1. $\length(\nil) = \zero$.
2. $\length(\cons(a,\nil)) = \next(\zero)$.
3. $\length(\cons(a,\cons(b,\nil))) = \next(\next(\zero))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \length(\nil) \\
 & = & \foldr{\zero}{\varphi}(\nil) \\
 & = & \zero
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \length(\cons(a,\nil)) \\
 & = & \next(\length(\nil)) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \length(\cons(a,\cons(b,\nil))) \\
 & = & \next(\length(\cons(b,\nil))) \\
 & = & \next(\next(\zero))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\length$ is invariant over $\rev$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have the following.

1. $\length(\snoc(a,x)) = \next(\length(x))$.
2. $\length(\rev(x)) = \length(x)$.
</p></div>

<div class="proof"><p>
1. We have $$\length(\snoc(a,x)) = \length(\cons(a,x)) = \next(\length(x))$$ as claimed.
2. We proceed by list induction. For the base case $x = \nil$, it suffices to note that $\rev(\nil) = \nil$. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\rev(\cons(a,x))) \\
 & = & \length(\snoc(a,\rev(x))) \\
 & = & \next(\length(\rev(x))) \\
 & = & \next(\length(x)) \\
 & = & \length(\cons(a,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\length$ turns $\cat$ into $\nplus$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\length(\cat(x,y)) = \nplus(\length(x),\length(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \length(\cat(x,\nil)) \\
 & = & \length(x) \\
 & = & \nplus(\length(x),\zero) \\
 & = & \nplus(\length(x),\length(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\cat(x,\cons(a,y))) \\
 & = & \length(\cat(\snoc(a,x),y)) \\
 & = & \nplus(\length(\snoc(a,x)),\length(y)) \\
 & = & \nplus(\next(\length(x)),\length(y)) \\
 & = & \nplus(\length(x),\next(\length(y))) \\
 & = & \nplus(\length(x),\length(\cons(a,y)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

> withTypeOf :: a -> a -> a
> withTypeOf x _ = x

Here are our property tests for $\length$.

> -- length(cons(a,x)) == length(cons(b,x))
> _test_length_cons :: (ListOf t, Eq a) => t a -> a -> a -> t a -> Bool
> _test_length_cons _ a b x =
>   (length (cons a x)) == (length (cons b x))
> 
> 
> -- length(cons(a,x)) == length(snoc(a,x))
> _test_length_cons_snoc :: (ListOf t, Eq a) => t a -> a -> t a -> Bool
> _test_length_cons_snoc _ a x =
>   (length (cons a x)) == (length (snoc a x))
> 
> 
> -- length(cons(a,x)) == next(length(x))
> _test_length_cons_next :: (ListOf t, Eq a) => t a -> a -> t a -> Bool
> _test_length_cons_next _ a x =
>   (length (cons a x)) == next (length x)
> 
> 
> -- length(cons(a,nil)) == next(zero)
> _test_length_single :: (ListOf t, Eq a) => t a -> a -> Bool
> _test_length_single z a =
>   let nil' = nil `withTypeOf` z in
>   (length (cons a nil')) == next zero
> 
> 
> -- length(cons(a,cons(b,nil))) == next(next(zero))
> _test_length_double :: (ListOf t, Eq a) => t a -> a -> a -> Bool
> _test_length_double z a b =
>   let nil' = nil `withTypeOf` z in
>   (length (cons a (cons b nil'))) == next (next zero)
> 
> 
> -- length(snoc(a,x)) == next(length(x))
> _test_length_snoc_next :: (ListOf t, Eq a) => t a -> a -> t a -> Bool
> _test_length_snoc_next _ a x =
>   (length (snoc a x)) == next (length x)
> 
> 
> -- length(rev(x)) == length(x)
> _test_length_rev :: (ListOf t, Eq a) => t a -> t a -> Bool
> _test_length_rev _ x =
>   (length (rev x)) == (length x)
> 
> 
> -- length(cat(x,y)) == plus(length(x),length(y))
> _test_length_cat :: (ListOf t, Eq a) => t a -> t a -> t a -> Bool
> _test_length_cat _ x y =
>   (length (cat x y)) == (plus (length x) (length y))

And the suite:

> -- run all tests for length
> _test_length :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_length t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_length_cons t)
>   , quickCheckWith args (_test_length_cons_snoc t)
>   , quickCheckWith args (_test_length_cons_next t)
>   , quickCheckWith args (_test_length_single t)
>   , quickCheckWith args (_test_length_double t)
>   , quickCheckWith args (_test_length_snoc_next t)
>   , quickCheckWith args (_test_length_rev t)
>   , quickCheckWith args (_test_length_cat t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_length :: IO ()
> main_length = _test_length (nil :: List Bool) 20 100