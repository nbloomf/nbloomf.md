---
title: Unzip
author: nbloomf
date: 2017-05-07
tags: arithmetic-made-difficult, literate-haskell
---

> module Unzip
>   ( unzip, _test_unzip, main_unzip
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length, head, tail, map, zip, unzip)
> 
> import NaturalNumbers
> import Plus
> import MaxAndMin
>
> import Lists
> import Reverse
> import Cat
> import Length
> import At
> import Map
> import UnfoldN
> import Range
> import Zip
> 
> import Test.QuickCheck

Today we will define a kind of one-sided inverse of $\zip$, called $\unzip$. Recall that $\zip$ has signature $$\lists{A} \times \lists{B} \rightarrow \lists{A \times B}.$$ An inverse will then have signature $$\lists{A \times B} \rightarrow \lists{A} \times \lists{B},$$ and should "undo" the zipping. As usual we'd like to define this as a fold if possible; to that end we need $\varepsilon : \lists{A} \times \lists{B}$ and $$\varphi : (A \times B) \times (\lists{A} \times \lists{B}) \rightarrow \lists{A} \times \lists{B}$$ such that
$$\begin{eqnarray*}
 &   & (\nil,\nil) \\
 & = & \unzip(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil) \\
 & = & \varepsilon
\end{eqnarray*}$$
and if $\unzip(x) = (u,v)$, then
$$\begin{eqnarray*}
 &   & (\cons(a,u),\cons(b,v)) \\
 & = & \unzip(\cons((a,b),x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons((a,b),x)) \\
 & = & \varphi((a,b),\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi((a,b),\unzip(x)) \\
 & = & \varphi((a,b),(u,v)).
\end{eqnarray*}$$
With this in mind, we define $\unzip$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\varphi : (A \times B) \times (\lists{A} \times \lists{B}) \rightarrow \lists{A} \times \lists{B}$ by $$\varphi((a,b),(u,v)) = (\cons(a,u),\cons(b,v).$$ We then define $\unzip : \lists{A \times B} \rightarrow \lists{A} \times \lists{B}$ by $$\unzip(x) = \foldr{(\nil,\nil)}{\varphi}(x).$$

In Haskell:

> unzip :: (ListOf t) => t (a,b) -> (t a, t b)
> unzip = foldr (nil,nil) phi
>   where
>     phi (a,b) (u,v) = (cons a u, cons b v)

</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. We have the following for all $x \in \lists{A \times B}$ and $(a,b) \in A \times B$.

1. $\unzip(\nil) = (\nil,\nil)$.
2. If $\unzip(x) = (u,v)$, then $\unzip(\cons((a,b),x) = (\cons(a,u),\cons(b,v))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \unzip(\nil) \\
 & = & \foldr{(\nil,\nil)}{\varphi}(\nil) \\
 & = & (\nil,\nil)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \unzip(\cons((a,b),x)) \\
 & = & \foldr{(\nil,\nil}{\varphi}(\cons((a,b),x)) \\
 & = & \varphi((a,b),\foldr{(\nil,\nil)}{\varphi}(x)) \\
 & = & \varphi((a,b),\unzip(x)) \\
 & = & \varphi((a,b),(u,v)) \\
 & = & (\cons(a,u),\cons(b,v))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now $\zip$ undoes $\unzip$ as expected.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. For all $x \in \lists{A \times B}$, we have $$\zip(\unzip(x)) = x.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\unzip(x)) \\
 & = & \zip(\unzip(\nil)) \\
 & = & \zip(\nil,\nil) \\
 & = & \nil \\
 & = & x
\end{eqnarray*}$$
as needed. Suppose now that the result holds for some $x$ and let $a \in A$ and $b \in B$. Let $(u,v) = \unzip(x)$. Now
$$\begin{eqnarray*}
 &   & \zip(\unzip(\cons((a,b),x)) \\
 & = & \zip(\cons(a,u),\cons(b,v)) \\
 & = & \cons((a,b),\zip(u,v)) \\
 & = & \cons((a,b),\zip(\unzip(x))) \\
 & = & \cons((a,b),x)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

(Note that the reverse composition $\unzip(\zip(x,y)) = (x,y),$ although it makes sense type-wise, does not hold for all $x$ and $y$ since $\zip$ truncates its longer argument.)

$\unzip$ interacts with $\swap$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets and $x \in \lists{A \times B}$. Then we have $$\swap(\unzip(x)) = \unzip(\map(\swap)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \swap(\unzip(x)) \\
 & = & \swap(\unzip(\nil)) \\
 & = & \swap(\nil,\nil) \\
 & = & (\nil,\nil) \\
 & = & \unzip(\nil) \\
 & = & \unzip(\map(\swap)(\nil)) \\
 & = & \unzip(\map(\swap)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $(a,b) \in A \times B$. Suppose $(u,v) = \unzip(x)$; by the inductive hypothesis we have $(v,u) = \unzip(\map(\swap)(x))$. Now
$$\begin{eqnarray*}
 &   & \unzip(\map(\swap)(\cons((a,b),x))) \\
 & = & \unzip(\cons(\swap(a,b),\map(\swap)(x))) \\
 & = & \unzip(\cons((b,a),\map(\swap)(x))) \\
 & = & (\cons(b,v),\cons(a,u)) \\
 & = & \swap(\cons(a,u),\cons(b,v)) \\
 & = & \swap(\unzip(\cons((a,b),x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

One more.

<div class="result">
<div class="thm"><p>
Let $A$, $B$, $U$, and $V$ be sets, with $f : A \rightarrow U$ and $g : B \rightarrow V$. For all $x \in \lists{A \times B}$ we have $$\unzip(\map(\pair(f,g))(x)) = \pair(\map(f),\map(g))(\unzip(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \unzip(\map(\pair(f,g))(\nil)) \\
 & = & \unzip(\nil) \\
 & = & (\nil,\nil) \\
 & = & (\map(f)(\nil),\map(g)(\nil)) \\
 & = & \pair(\map(f),\map(g))(\nil,\nil) \\
 & = & \pair(\map(f),\map(g))(\unzip(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $(a,b) \in A \times B$. Say $(u,v) = \unzip(x)$. Letting $\varphi$ be as in the definition of $\unzip$ and using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \pair(\map(f),\map(g))(\unzip(\cons((a,b),x))) \\
 & = & \pair(\map(f),\map(g))(\cons(a,u),\cons(b,v)) \\
 & = & (\map(f)(\cons(a,u)),\map(g)(\cons(b,v))) \\
 & = & (\cons(f(a),\map(f)(u)),\cons(g(b),\map(g)(v))) \\
 & = & \varphi((f(a),g(b)),(\map(f)(u),\map(g)(v))) \\
 & = & \varphi((f(a),g(b)),\pair(\map(f),\map(g))(u,v)) \\
 & = & \varphi((f(a),g(b)),\pair(\map(f),\map(g))(\unzip(x))) \\
 & = & \varphi((f(a),g(b)),\unzip(\map(\pair(f,g))(x))) \\
 & = & \varphi(\pair(f,g)(a,b),\unzip(\map(\pair(f,g))(x))) \\
 & = & \varphi(\pair(f,g)(a,b),\foldr{(\nil,\nil)}{\varphi}(\map(\pair(f,g))(x))) \\
 & = & \foldr{(\nil,\nil)}{\varphi}(\cons(\pair(f,g)(a,b),\map(\pair(f,g))(x))) \\
 & = & \foldr{(\nil,\nil)}{\varphi}(\map(\pair(f,g))(\cons((a,b),x))) \\
 & = & \unzip(\map(\pair(f,g))(\cons((a,b),x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\unzip$.

> -- zip(unzip(x)) == x
> _test_unzip_zip :: (ListOf t, Eq a)
>   => t a -> t (a,a) -> Bool
> _test_unzip_zip _ x =
>   ((uncurry zip) (unzip x)) `listEq` x
> 
> 
> -- swap(unzip(x)) == unzip(map(swap)(x))
> _test_unzip_swap :: (ListOf t, Eq a)
>   => t a -> t (a,a) -> Bool
> _test_unzip_swap _ x =
>   (\(a,b) (c,d) -> (listEq a c) && (listEq b d))
>     (unzip (map swap x))
>     (swap (unzip x))

And the suite:

> -- run all tests for unzip
> _test_unzip :: (ListOf t, Arbitrary (t n), Show (t n), Natural n, Arbitrary n, Show n, Arbitrary (t (n,n)), Show (t (n,n)))
>   => t n -> n -> Int -> Int -> IO ()
> _test_unzip t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_unzip_zip t)
>   , quickCheckWith args (_test_unzip_swap t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_unzip :: IO ()
> main_unzip = _test_unzip (nil :: List Nat) (zero :: Nat) 20 100
