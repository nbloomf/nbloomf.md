---
title: Zip
author: nbloomf
date: 2017-05-06
tags: arithmetic-made-difficult, literate-haskell
---

> module Zip
>   ( --zip, zipPad, _test_zip, main_zip
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length, head, tail, map, zip)
> 
> import NaturalNumbers
> import Plus
>
> import Lists
> import Reverse
> import Cat
> import Length
> import At
> import Map
> import UnfoldN
> import Range
> 
> import Test.QuickCheck

Today we'll define a really useful function on lists called $\zip$. This map will take two lists, one in $\lists{A}$ and one in $\lists{B}$, and return a list in $\lists{A \times B}$. In progress, $\zip$ping two lists looks something like this:
$$\begin{array}{ccccccccccc}
          &   &           &   &           &           & a_4 & - & a_5 &   &     \\
          &   &           &   &           & \diagup   &     &   &     &   &     \\
(a_1,b_1) & - & (a_2,b_2) & - & (a_3,b_3) &           &     &   &     &   &     \\
          &   &           &   &           & \diagdown &     &   &     &   &     \\
          &   &           &   &           &           & b_4 & - & b_5 & - & b_6
\end{array}$$
Hence the name $\zip$ -- it looks like a zipper in action. Two big questions have to be resolved. First, it seems clear what $\zip$ should do if we give it two lists with the same length. But what if we try to zip two lists of different lengths? I can see two basic strategies. On one hand we can just truncate to the length of the shortest list. Another idea is to *pad* the shorter list to the length of the longer. These are both useful but essentially different behaviors, so we will define two different functions to handle them. The truncation strategy will be called $\zip$ and the padding strategy will be called $\zipPad$.

The second problem to address is exactly how to implement such a function. The signature of $\zip$ is $$\lists{A} \times \lists{B} \rightarrow \lists{A \times B}.$$ At the moment we have only two essentially different recursion operators on $\lists{-}$. There's $\foldr{-}{-}$, with signature $$\lists{A} \rightarrow B,$$ and $\unfoldN(-,-,-)$, with signature $$(A \rightarrow \ast + A \times B) \times \nats \times A \rightarrow \lists{B}.$$ Which to use? $\unfoldN$ has the right output type, and it is reasonably straightforward to define $\zip$ using $\unfoldN$ (try it!). But $\unfoldN$ has a drawback -- we have to compute an upper bound on the length of the output in advance. In the case of $\zip(x,y)$, that bound is $\nmin(\length(x),\length(y))$. We prefer to avoid doing too much computation in the $\nats$ argument of $\unfoldN$, so that strategy is out.

But $\foldr{-}{-}$ takes only one input list. The usual way to turn a function of one argument into a function of two arguments is with currying -- that is, make the *return* type a function. So we should look for appropriate $\varepsilon$ and $\varphi$ so that $$\foldr{\varepsilon}{\varphi} : \lists{A} \rightarrow \lists{A \times B}^{\lists{B}}$$ uncurries to $$\zip : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$$ as we want. Now we should have $$\varepsilon : \lists{A \times B}^{\lists{B}},$$ and intuitively,
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \zip(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y).
\end{eqnarray*}$$

Similarly, we want $$\varphi : \lists{A} \times \lists{A \times B}^{\lists{B}} \rightarrow \lists{A \times B}^{\lists{B}},$$ with
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \zip(\cons(a,x),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\nil) \\
 & = & \varphi(a,\zip(x,-))(\nil)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \cons((a,b),\zip(x,y)) \\
 & = & \zip(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \varphi(a,\zip(x,-))(\cons(b,y)).
\end{eqnarray*}$$

Once again, the recursion operators allow us to be sloppy at first. :) With these constraints in hand, we define $\zip$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\varepsilon : \lists{A \times B}^{\lists{B}}$ by $$\varepsilon(y) = \nil$$ and define $\varphi : \lists{A} \times \lists{A \times B}^{\lists{B}} \rightarrow \lists{A\times B}^{\lists{B}}$ by $$\varphi(x,f)(z) = \left\{\begin{array}{ll} \nil & \mathrm{if}\ z = \nil \\ \cons((x,y),f(w)) & \mathrm{if}\ z = \cons(y,w). \end{array}\right.$$ We then define $\zip : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$ by $$\zip(x,y) = \foldr{\varepsilon}{\varphi}(x)(y).$$
</p></div>
</div>

We can implement $\zip$ directly with $\foldr{-}{-}$ as in the definition.

```haskell

> zip' :: (ListOf t) => t a -> t b -> t (a,b)
> zip' = foldr epsilon phi
>   where
>     phi :: (ListOf t) => a -> (t b -> t (a,b)) -> t b -> t (a,b)
>     phi x f z = case listShape z of
>       Nil       -> nil
>       Cons y ys -> cons (x,y) (f ys)
>
>     epsilon :: (ListOf t) => t b -> t (a,b)
>     epsilon z = nil

```

This does the job. But it's also a little awkward; it constructs an intermediate list of functions. The following result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then we have the following for all $a \in A$, $x \in \lists{A}$, $b \in B$, and $y \in \lists{B}$.

1. $\zip(\nil,y) = \nil$.
2. $\zip(x,\nil) = \nil$.
3. $\zip(\cons(a,x),\cons(b,y)) = \cons((a,b),\zip(x,y))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \zip(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We consider two cases: either $x = \nil$ or $x = \cons(d,w)$ for some $d \in A$ and $w \in \lists{A}$. Certainly if $x = \nil$ we have $$\zip(x,\nil) = \zip(\nil,\nil) = \nil$$ as claimed. Suppose then that $x = \cons(d,w)$; now we have
$$\begin{eqnarray*}
 &   & \zip(\cons(d,w),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(d,w))(\nil) \\
 & = & \varphi(d,\foldr{\varepsilon}{\varphi}(x))(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \zip(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \cons((a,b),\foldr{\varepsilon}{\varphi}(x)(y)) \\
 & = & \cons((a,b),\zip(x,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

> zip :: (ListOf t) => t a -> t b -> t (a,b)
> zip x y = case listShape x of
>   Nil       -> nil
>   Cons a as -> case listShape y of
>     Nil       -> nil
>     Cons b bs -> cons (a,b) (zip as bs)

$\zip$ will turn out to be pretty useful. Before establishing some properties for it, we need a few utility functions on pairs.

<div class="result">
<div class="defn"><p>
Let $A$, $B$, $U$, and $V$ be sets.

Define $\swap : A \times B \rightarrow B \times A$ by $$\swap(a,b) = (b,a).$$

Define $\pair : U^A \times V^B \rightarrow (U \times V)^{A \times B}$ by $$\pair(f,g)(a,b) = (f(a),g(b)).$$

In Haskell:

> swap :: (a,b) -> (b,a)
> swap (a,b) = (b,a)
> 
> pair :: (a -> u) -> (b -> v) -> (a,b) -> (u,v)
> pair f g (a,b) = (f a, g b)

</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then for all $x \in \lists{A}$ and $y \in \lists{B}$ we have $$\map(\swap)(\zip(x,y)) = \zip(y,x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zip(x,y)) \\
 & = & \map(\swap)(\zip(\nil,y)) \\
 & = & \map(\swap)(\nil) \\
 & = & \nil \\
 & = & \zip(y,\nil) \\
 & = & \zip(y,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y \in \lists{B}$ for some $x \in \lists{A}$, and let $a \in A$. Now we proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zip(\cons(a,x),y)) \\
 & = & \map(\swap)(\zip(\cons(a,x),\nil)) \\
 & = & \map(\swap)(\nil) \\
 & = & \nil \\
 & = & \zip(\nil,\cons(a,x)) \\
 & = & \zip(y,\cons(a,x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for $y$ and $\cons(a,x)$, and let $b \in B$. Using the induction hypotheses, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zip(\cons(a,x),\cons(b,y))) \\
 & = & \map(\swap)(\cons((a,b),\zip(x,y))) \\
 & = & \cons(\swap(a,b),\map(\swap)(\zip(x,y))) \\
 & = & \cons((b,a),\zip(y,x)) \\
 & = & \zip(\cons(b,y),\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$, $B$, $U$, and $V$ be sets, with functions $f : A \rightarrow U$ and $g : B \rightarrow V$. Then for all $x \in \lists{A}$ and $y \in \lists{B}$, we have $$\map(\pair(f,g))(\zip(x,y)) = \zip(\map(f)(x),\map(g)(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zip(x,y)) \\
 & = & \map(\pair(f,g))(\zip(\nil,y)) \\
 & = & \map(\pair(f,g))(\nil) \\
 & = & \nil \\
 & = & \zip(\nil,\map(g)(y)) \\
 & = & \zip(\map(f)(\nil),\map(g)(y)) \\
 & = & \zip(\map(f)(x),\map(g)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for all $y$ for some $x \in \lists{A}$, and let $a \in A$. We now proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zip(\cons(a,x),y)) \\
 & = & \map(\pair(f,g))(\zip(\cons(a,x),\nil)) \\
 & = & \map(\pair(f,g))(\nil) \\
 & = & \nil \\
 & = & \zip(\map(f)(\cons(a,x)),\nil) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(\nil)) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $y \in \lists{B}$. Now we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zip(\cons(a,x),\cons(b,y))) \\
 & = & \map(\pair(f,g))(\cons((a,b),\zip(x,y))) \\
 & = & \cons(\pair(f,g)(a,b),\map(\pair(f,g))(\zip(x,y))) \\
 & = & \cons(\pair(f,g)(a,b),\zip(\map(f)(x),\map(g)(y))) \\
 & = & \cons((f(a),g(b)),\zip(\map(f)(x),\map(g)(y))) \\
 & = & \zip(\cons(f(a),\map(f)(x)),\cons(g(b),\map(g)(y))) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(\cons(b,y)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets.
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

> -- map(swap)(zip(x,y)) = zip(y,x)
> _test_zip_swap :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_zip_swap _ x y =
>   (map swap (zip x y)) `listEq` (zip y x)

And the suite:

> -- run all tests for zip
> _test_zip :: (ListOf t, Arbitrary (t n), Show (t n), Natural n, Arbitrary n, Show n)
>   => t n -> n -> Int -> Int -> IO ()
> _test_zip t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_zip_swap t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_zip :: IO ()
> main_zip = _test_zip (nil :: List Nat) (zero :: Nat) 20 100
