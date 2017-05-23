---
title: Filter
author: nbloomf
date: 2017-05-13
tags: arithmetic-made-difficult, literate-haskell
---

> module Filter
>   ( filter, _test_filter, main_filter
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
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll nail down $\filter$, which takes a list and a predicate on the items and "filters out" the items which satisfy the predicate. $\filter$ should have a signature like $$\bool^A \times \lists{A} \rightarrow \lists{A}.$$ As usual, we want to define $\filter$ as a fold; say $$\filter(p,x) = \foldr{\varepsilon}{\varphi}(x).$$ Where on the right hand side of that equation should the $p$ parameter go? Lets think out loud for a moment. On the one hand, we want
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \filter(p,\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil) \\
 & = & \varepsilon.
\end{eqnarray*}$$
On the other hand, we want
$$\begin{eqnarray*}
 &   & \filter(p,\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(a,\filter(p,x)).
\end{eqnarray*}$$
Intuitively, if $p(a)$ is $\btrue$ we want $$\filter(p,\cons(a,x)) = \cons(a,\filter(p,x)),$$ while if $p(a)$ is $\bfalse$ we want $$\filter(p,\cons(a,x)) = \filter(p,x).$$ With this in mind we define $\filter$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : \bool^A \rightarrow A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(p)(a,w) = \left\{ \begin{array}{ll} \cons(a,w) & \mathrm{if}\ p(a) = \btrue \\ w & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$ Now define $$\filter : \bool^A \times \lists{A} \rightarrow \lists{A}$$ by $$\filter(p,x) = \foldr{\nil}{\varphi(p)}(x).$$
</p></div>
</div>

We can translate $\filter$ to Haskell directly as follows:

> filter' :: (List t) => (a -> Bool) -> t a -> t a
> filter' p x = foldr nil (phi p) x
>   where
>     phi q a w = if q a ==== True
>       then cons a w
>       else w

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a function. Then we have the following.

1. $\filter(p,\nil) = \nil$.
2. $$\filter(p,\cons(a,x)) = \left\{\begin{array}{ll} \cons(a,\filter(p,x)) & \mathrm{if}\ p(a) = \btrue \\ \filter(p,x) & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \filter(p,\nil) \\
 & = & \foldr{\nil}{\varphi(p)}(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\cons(a,x)) \\
 & = & \foldr{\nil}{\varphi(p)}(\cons(a,x)) \\
 & = & \varphi(p)(a,\foldr{\nil}{\varphi(p)}(x)) \\
 & = & \cons(a,\foldr{\nil}{\varphi(p)}(x)) \\
 & = & \cons(a,\filter(p,x)),
\end{eqnarray*}$$
while if $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\cons(a,x)) \\
 & = & \foldr{\nil}{\varphi(p)}(\cons(a,x)) \\
 & = & \varphi(p)(a,\foldr{\nil}{\varphi(p)}(x)) \\
 & = & \foldr{\nil}{\varphi(p)}(x) \\
 & = & \filter(p,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> filter :: (List t) => (a -> Bool) -> t a -> t a
> filter p x = case listShape x of
>   Nil      -> nil
>   Cons a w -> if p a ==== True
>     then cons a (filter p w)
>     else filter p w

As we might expect, the items in $\filter(p,x)$ all satisfy $p$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$ we have $$\all(p,\filter(p,x)) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p,\nil)) \\
 & = & \all(p,\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p,\cons(a,x))) \\
 & = & \all(p,\cons(a,\filter(p,x))) \\
 & = & \and(p(a),\all(p,\filter(p,x))) \\
 & = & \and(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed, while if $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \all(p,\filter(p,\cons(a,x))) \\
 & = & \all(p,\filter(p,x)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\filter$ interacts with $\snoc$ and $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x \in \lists{A}$, we have the following.

1. $$\filter(p,\snoc(a,x)) = \left\{\begin{array}{ll} \snoc(a,\filter(p,x)) & \mathrm{if}\ p(a) = \btrue \\ \filter(p,x) & \mathrm{if}\ p(a) = \bfalse. \end{array}\right.$$
2. $\filter(p,\rev(x)) = \rev(\filter(p,x))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, if $p(a) = \btrue$ we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\nil)) \\
 & = & \filter(p,\cons(a,\nil)) \\
 & = & \cons(a,\filter(p,\nil)) \\
 & = & \cons(a,\nil) \\
 & = & \snoc(a,\nil)
\end{eqnarray*}$$
as claimed, while if $p(a) = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\nil)) \\
 & = & \filter(p,\cons(a,\nil)) \\
 & = & \filter(p,\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. If $p(a) = p(b) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\cons(b,x))) \\
 & = & \filter(p,\cons(b,\snoc(a,x))) \\
 & = & \cons(b,\filter(p,\snoc(a,x))) \\
 & = & \cons(b,\snoc(a,\filter(p,x))) \\
 & = & \snoc(a,\cons(b,\filter(p,x))) \\
 & = & \snoc(a,\filter(p,\cons(b,x)))
\end{eqnarray*}$$
as needed. If $p(a) = \btrue$ and $p(b) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\cons(b,x))) \\
 & = & \filter(p,\cons(b,\snoc(a,x))) \\
 & = & \filter(p,\snoc(a,x)) \\
 & = & \snoc(a,\filter(p,x)) \\
 & = & \snoc(a,\filter(p,\cons(b,x)))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$ and $p(b) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\cons(b,x))) \\
 & = & \filter(p,\cons(b,\snoc(a,x))) \\
 & = & \cons(b,\filter(p,\snoc(a,x))) \\
 & = & \cons(b,\filter(p,x)) \\
 & = & \filter(p,\cons(b,x))
\end{eqnarray*}$$
as needed. Finally, if $p(a) = p(b) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\snoc(a,\cons(b,x))) \\
 & = & \filter(p,\cons(b,\snoc(a,x))) \\
 & = & \filter(p,\snoc(a,x)) \\
 & = & \filter(p,x) \\
 & = & \filter(p,\cons(b,x))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\rev(\nil)) \\
 & = & \filter(p,\nil) \\
 & = & \nil \\
 & = & \rev(\nil) \\
 & = & \rev(\filter(p,\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \rev(\filter(p,\cons(a,x))) \\
 & = & \rev(\cons(a,\filter(p,x))) \\
 & = & \snoc(a,\rev(\filter(p,x))) \\
 & = & \snoc(a,\filter(p,\rev(x))) \\
 & = & \filter(p,\snoc(a,\rev(x))) \\
 & = & \filter(p,\rev(\cons(a,x)))
\end{eqnarray*}$$
as claimed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \rev(\filter(p,\cons(a,x))) \\
 & = & \rev(\filter(p,x)) \\
 & = & \filter(p,\rev(x)) \\
 & = & \filter(p,\snoc(a,\rev(x))) \\
 & = & \filter(p,\rev(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$ a predicate. For all $x,y \in \lists{A}$ we have $$\filter(p,\cat(x,y)) = \cat(\filter(p,x),\filter(p,y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\cat(x,y)) \\
 & = & \filter(p,\cat(\nil,y)) \\
 & = & \filter(p,y) \\
 & = & \cat(\nil,\filter(p,y)) \\
 & = & \cat(\filter(p,\nil),\filter(p,y)) \\
 & = & \cat(\filter(p,x),\filter(p,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\cat(\cons(a,x),y)) \\
 & = & \filter(p,\cons(a,\cat(x,y))) \\
 & = & \cons(a,\filter(p,\cat(x,y))) \\
 & = & \cons(a,\cat(\filter(p,x),\filter(p,y))) \\
 & = & \cat(\cons(a,\filter(p,x)),\filter(p,y)) \\
 & = & \cat(\filter(p,\cons(a,x)),\filter(p,y))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \filter(p,\cat(\cons(a,x),y)) \\
 & = & \filter(p,\cons(a,\cat(x,y))) \\
 & = & \filter(p,\cat(x,y)) \\
 & = & \cat(\filter(p,x),\filter(p,y)) \\
 & = & \cat(\filter(p,\cons(a,x)),\filter(p,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\filter$:

> -- filter(p,x) == filter'(p,x)
> _test_filter_alt :: (List t, Equal a)
>   => t a -> (a -> Bool) -> ListOf t a -> Bool
> _test_filter_alt _ p x =
>   (filter p x) ==== (filter' p x)
> 
> 
> -- all(p,filter(p,x)) == true
> _test_filter_all :: (List t, Equal a)
>   => t a -> (a -> Bool) -> ListOf t a -> Bool
> _test_filter_all _ p x =
>   (all p (filter p x)) ==== True
> 
> 
> -- filter(p,snoc(a,x)) == if(p(a),snoc(a,filter(p,x)),filter(p,x))
> _test_filter_snoc :: (List t, Equal a)
>   => t a -> (a -> Bool) -> a -> ListOf t a -> Bool
> _test_filter_snoc _ p a x =
>   if p a ==== True
>     then (filter p (snoc a x)) ==== (snoc a (filter p x))
>     else (filter p (snoc a x)) ==== (filter p x)
> 
> 
> -- filter(p,rev(x)) == rev(filter(p,x))
> _test_filter_rev :: (List t, Equal a)
>   => t a -> (a -> Bool) -> ListOf t a -> Bool
> _test_filter_rev _ p x =
>   (filter p (rev x)) ==== (rev (filter p x))
> 
> 
> -- filter(p,cat(x,y)) == cat(filter(p,x),filter(p,y))
> _test_filter_cat :: (List t, Equal a)
>   => t a -> (a -> Bool) -> ListOf t a -> ListOf t a -> Bool
> _test_filter_cat _ p x y =
>   (filter p (cat x y)) ==== (cat (filter p x) (filter p y))

And the suite:

> -- run all tests for filter
> _test_filter ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_filter t maxSize numCases = do
>   testLabel ("filter: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_filter_alt t)
>   runTest args (_test_filter_all t)
>   runTest args (_test_filter_snoc t)
>   runTest args (_test_filter_rev t)
>   runTest args (_test_filter_cat t)

And ``main``:

> main_filter :: IO ()
> main_filter = do
>   _test_filter (nil :: ConsList Bool)  20 100
>   _test_filter (nil :: ConsList Unary) 20 100
