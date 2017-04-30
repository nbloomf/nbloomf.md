---
title: Map
author: nbloomf
date: 2017-04-29
tags: arithmetic-made-difficult, literate-haskell
---

> module Map
>   ( map, _test_map, main_map
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
> 
> import Test.QuickCheck

Today we'll explore one of the most useful functions on $\lists{A}$: $\map$. What $\map$ does is take a function $A \rightarrow B$ and a list in $\lists{A}$, and apply the function "itemwise" to get a list in $\lists{B}$.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\varphi : B^A \rightarrow A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(f)(a,x) = \cons(f(a),x).$$ We then define $\map : B^A \rightarrow \lists{A} \rightarrow \lists{B}$ by $$\map(f) = \foldr{\nil}{\varphi(f)}.$$

In Haskell:

> map :: (ListOf t) => (a -> b) -> t a -> t b
> map f = foldr nil (phi f)
>   where
>     phi g a x = cons (g a) x

</p></div>
</div>

(For the rest of this post we will let $\varphi$ be as in this definition.)

One way to think about $\map$ is that it fills in the following diagram.
$$\require{AMScd}
\begin{CD}
A @>{f}>> B\\
@V{\lists{\ast}}VV @VV{\lists{\ast}}V \\
\lists{A} @>>{\map(f)}> \lists{B}
\end{CD}$$
This looks an awful lot like a functor diagram. Recall that given two categories, a functor associates objects to objects and morphisms to morphisms, preserving $\id$ and composition. And indeed, $\map$ is the morphism part of the $\lists{\ast}$ functor.

$\map$ takes $\id_A$ to $\id_{\lists{A}}$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Then we have $$\map(\id_A) = \id_{\lists{A}}.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \varphi(\id_A)(a,x) \\
 & = & \cons(\id_A(a),x) \\
 & = & \cons(a,x);
\end{eqnarray*}$$
that is, $\varphi(\id_A) = \cons$. So we have
$$\begin{eqnarray*}
 &   & \map(\id_A) \\
 & = & \foldr{\nil}{\varphi(\id_A)} \\
 & = & \foldr{\nil}{\cons} \\
 & = & \id_{\lists{A}}
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\map$ preserves composition:

<div class="result">
<div class="thm"><p>
Let $A$, $B$, and $C$ be sets, with maps $f : A \rightarrow B$ and $g : B \rightarrow C$. Then $$\map(g \circ f) = \map(g) \circ \map(f).$$
</p></div>

<div class="proof"><p>
We will show that $$\map(g \circ f)(x) = (\map(g) \circ \map(f))(x)$$ for all $x \in \lists{A}$, proceeding by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(x) \\
 & = & (\map(g) \circ \map(f))(\nil) \\
 & = & \map(g)(\map(f)(\nil)) \\
 & = & \map(g)(\foldr{\nil}{\varphi(f)}(\nil)) \\
 & = & \map(g)(\nil) \\
 & = & \foldr{\nil}{\varphi(g)}(\nil) \\
 & = & \nil \\
 & = & \foldr{\nil}{\varphi(g \circ f)}(\nil) \\
 & = & \map(g \circ f)(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(\cons(a,x)) \\
 & = & \map(g)(\map(f)(\cons(a,x))) \\
 & = & \map(g)(\foldr{\nil}{\varphi(f)}(\cons(a,x))) \\
 & = & \map(g)(\varphi(f)(a,\foldr{\nil}{\varphi(f)}(x))) \\
 & = & \map(g)(\cons(f(a),\foldr{\nil}{\varphi(f)}(x))) \\
 & = & \map(g)(\cons(f(a),\map(f)(x))) \\
 & = & \foldr{\nil}{\varphi(g)}(\cons(f(a),\map(f)(x))) \\
 & = & \varphi(g)(f(a),\foldr{\nil}{\varphi(g)}(\map(f)(x))) \\
 & = & \cons(g(f(a)),\foldr{\nil}{\varphi(g)}(\map(f)(x))) \\
 & = & \cons(g(f(a)),\map(g)(\map(f)(x))) \\
 & = & \cons((g \circ f)(a),(\map(g) \circ \map(f))(x)) \\
 & = & \cons((g \circ f)(a),\map(g \circ f)(x)) \\
 & = & \varphi(g \circ f)(a,\map(g \circ f)(x)) \\
 & = & \varphi(g \circ f)(a,\foldr{\nil}{\varphi(g \circ f)}(x)) \\
 & = & \foldr{\nil}{g \circ f}(\cons(a,x)) \\
 & = & \map(g \circ f)(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\map(f)$ respects $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x,y \in \lists{A}$, we have $$\map(f)(\cat(x,y)) = \cat(\map(f)(x),\map(f)(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\cat(x,y)) \\
 & = & \map(f)(\cat(\nil,y)) \\
 & = & \map(f)(y) \\
 & = & \cat(\nil,\map(f)(y)) \\
 & = & \cat(\map(f)(\nil),\map(f)(y)) \\
 & = & \cat(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\cat(\cons(a,x),y)) \\
 & = & \map(f)(\cons(a,\cat(x,y))) \\
 & = & \cons(f(a),\map(f)(\cat(x,y))) \\
 & = & \cons(f(a),\cat(\map(f)(x),\map(f)(y))) \\
 & = & \cat(\cons(f(a),\map(f)(x)),\map(f)(y)) \\
 & = & \cat(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\map(f)$ respects $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\rev(x)) = \rev(\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\rev(x)) \\
 & = & \map(f)(\rev(\nil)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \rev(\nil) \\
 & = & \rev(\map(f)(\nil)) \\
 & = & \rev(\map(f)(x)) \\
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for some $x \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\rev(\cons(a,x))) \\
 & = & \map(f)(\rev(\cons(a,\cat(\nil,x)))) \\
 & = & \map(f)(\rev(\cat(\cons(a,\nil),x))) \\
 & = & \map(f)(\cat(\rev(x),\rev(\cons(a,\nil)))) \\
 & = & \cat(\map(f)(\rev(x)),\map(f)(\rev(\cons(a,\nil)))) \\
 & = & \cat(\rev(\map(f)(x)),\map(f)(\cons(a,\nil))) \\
 & = & \cat(\rev(\map(f)(x)),\cons(f(a),\map(f)(\nil))) \\
 & = & \cat(\rev(\map(f)(x)),\cons(f(a),\nil)) \\
 & = & \cat(\rev(\map(f)(x)),\rev(\cons(f(a),\nil))) \\
 & = & \cat(\rev(\map(f)(x)),\rev(\map(f)(\cons(a,\nil)))) \\
 & = & \rev(\cat(\map(f)(\cons(a,\nil)),\map(f)(x))) \\
 & = & \rev(\cat(\cons(f(a),\map(f)(\nil)),\map(f)(x))) \\
 & = & \rev(\cat(\cons(f(a),\nil),\map(f)(x))) \\
 & = & \rev(\cons(f(a),\cat(\nil,\map(f)(x)))) \\
 & = & \rev(\cons(f(a),\map(f)(x))) \\
 & = & \rev(\map(f)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\map(f)$ interacts with $\at$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. Let $x \in \lists{A}$, and suppose $\at(x,k) \neq \ast$. Then we have $$\at(\map(f)(x),k) = f(\at(x,k)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that $\at(x,k) = \ast$ for all $k$, so the implication holds vacuously. For the inductive step, suppose the implication holds for all $k$ for some $x$. Now let $a \in A$. We consider three possibilities for $k$: either $k = \zero$, $k = \next(\zero)$, or $k = \next(\next(\zero))$.

If $k = \zero$, then $\at(\cons(a,x),k) = \ast$, and the implication holds vacuously.

Suppose $k = \next(\zero)$. Now $\at(\cons(a,x),k) \neq \ast$, and we have
$$\begin{eqnarray*}
 &   & f(\at(\cons(a,x),k)) \\
 & = & f(\at(\cons(a,x),\next(\zero)) \\
 & = & f(a) \\
 & = & \at(\cons(f(a),\map(f)(x)),\next(\zero)) \\
 & = & \at(\map(f)(\cons(a,x)),\next(\zero)) \\
 & = & \at(\map(f)(\cons(a,x)),k)
\end{eqnarray*}$$
as claimed.

Finally, suppose $k = \next(\next(m))$. Suppose further that $\at(\cons(a,x),k) \neq \ast$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & f(\at(\cons(a,x),k)) \\
 & = & f(\at(\cons(a,x),\next(\next(m)))) \\
 & = & f(\at(x,\next(m))) \\
 & = & \at(\map(f)(x),\next(m)) \\
 & = & \at(\cons(f(a),\map(f)(x)),\next(\next(m))) \\
 & = & \at(\map(f)(\cons(a,x)),k)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\map$ preserves $\length$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. Then for all $x \in \lists{A}$ we have $$\length(\map(f)(x)) = \length(x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \length(\map(f)(x)) \\
 & = & \length(\map(f)(\nil)) \\
 & = & \length(\nil) \\
 & = & \length(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\map(f)(\cons(a,x))) \\
 & = & \length(\cons(f(a),\map(f)(x))) \\
 & = & \next(\length(\map(f)(x))) \\
 & = & \next(\length(x)) \\
 & = & \length(\cons(a,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\map$.

> -- at(nil,k) == *
> _test_map_id :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_map_id _ x =
>   (map id x) `listEq` x

And the suite:

> -- run all tests for map
> _test_map :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a), Natural n, Arbitrary n, Show n)
>   => t a -> n -> Int -> Int -> IO ()
> _test_map t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_map_id t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_map :: IO ()
> main_map = _test_map (nil :: List Bool) (zero :: Nat) 20 100
