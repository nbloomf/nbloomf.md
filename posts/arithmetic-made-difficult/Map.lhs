---
title: Map
author: nbloomf
date: 2017-04-29
tags: arithmetic-made-difficult, literate-haskell
slug: map
---

> module Map
>   ( map, _test_map, main_map
>   ) where
> 
> import Prelude ()
> import Booleans
> import DisjointUnions
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Cat
> import Length
> import At

Today we'll explore one of the most useful functions on $\lists{A}$: $\map$. What $\map$ does is take a function $A \rightarrow B$ and a $\lists{A}$, and apply the function "itemwise" to get a $\lists{B}$.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\varphi : B^A \rightarrow A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(f)(a,x) = \cons(f(a),x).$$ We then define $\map : B^A \rightarrow \lists{A} \rightarrow \lists{B}$ by $$\map(f) = \foldr{\nil}{\varphi(f)}.$$

In Haskell:

> map :: (List t) => (a -> b) -> t a -> t b
> map f = foldr nil (phi f)
>   where
>     phi g a x = cons (g a) x

</p></div>
</div>

Since $\map$ is defined as a $\foldr{\ast}{\ast}$, it is the unique solution to a system of functional equations.

<div class="result">
<div class="thm"><p>
$\map(\alpha)$ is the unique solution $f : \lists{A} \rightarrow \lists{B}$ of the following equations for all $a \in A$ and $x \in \lists{A}$:
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \cons(\alpha(a),f(x))
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_map_nil :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> Bool)
> _test_map_nil t =
>   testName "map(f)(nil) == nil" $
>   \f -> eq (map f (nil `withTypeOf` t)) nil
> 
> 
> _test_map_cons :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> a -> t a -> Bool)
> _test_map_cons _ =
>   testName "map(f)(cons(a,x)) == cons(f(a),map(f)(x))" $
>   \f a x -> eq (map f (cons a x)) (cons (f a) (map f x))

</p></div>
</div>

One way to think about $\map$ is that it fills in the following diagram.
$$\require{AMScd}
\begin{CD}
A @>{f}>> B\\
@V{\lists{\ast}}VV @VV{\lists{\ast}}V \\
\lists{A} @>>{\map(f)}> \lists{B}
\end{CD}$$
This looks an awful lot like a functor diagram. Recall that given two categories, a functor associates objects to objects and morphisms to morphisms, preserving $\id$ and composition. And indeed, $\map$ is the morphism part of the $\lists{\ast}$ functor.

$\map$ takes $\id_A$ to $\id_{\lists{A}}$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Then we have $$\map(\id_A)(x) = x.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\id)(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \map(\id)(\cons(a,x)) \\
 & = & \cons(\id(a),\map(\id)(x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_id :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_map_id _ =
>   testName "map(id)(x) == x" $
>   \x -> eq (map id x) x

</p></div>
</div>

$\map$ preserves composition.

<div class="result">
<div class="thm"><p>
Let $A$, $B$, and $C$ be sets, with maps $f : A \rightarrow B$ and $g : B \rightarrow C$. For all $x \in \lists{A}$ we have $$\map(g \circ f)(x) = (\map(g) \circ \map(f))(x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(x) \\
 & = & (\map(g) \circ \map(f))(\nil) \\
 & = & \map(g)(\map(f)(\nil)) \\
 & = & \map(g)(\nil) \\
 & = & \nil \\
 & = & \map(g \circ f)(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & (\map(g) \circ \map(f))(\cons(a,x)) \\
 & = & \map(g)(\map(f)(\cons(a,x))) \\
 & = & \map(g)(\cons(f(a),\map(f)(x))) \\
 & = & \cons(g(f(a)),\map(g)(\map(f)(x))) \\
 & = & \cons((g \circ f)(a),(\map(g) \circ \map(f))(x)) \\
 & = & \cons((g \circ f)(a),(\map(g \circ f)(x)) \\
 & = & \map(g \circ f)(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_compose :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> (a -> a) -> t a -> Bool)
> _test_map_compose _ =
>   testName "map(g . f)(x) == (map(g) . map(f))(x)" $
>   \g f x -> eq (map (g . f) x) (((map g) . (map f)) x)

</p></div>
</div>

$\map(f)$ respects $\tail$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\map(f)(\tail(x)) = \tail(\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\nil)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \tail(\nil) \\
 & = & \tail(\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then
$$\begin{eqnarray*}
 &   & \map(f)(\tail(\cons(a,x))) \\
 & = & \map(f)(x) \\
 & = & \tail(\cons(f(a),\map(f)(x)) \\
 & = & \tail(\map(f)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_tail :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_map_tail _ =
>   testName "map(f)(tail(x)) == tail(map(f)(x))" $
>   \f x -> eq (map f (tail x)) (tail (map f x))

</p></div>
</div>

$\map(f)$ respects $\cat$.

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

<div class="test"><p>

> _test_map_cat :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> t a -> Bool)
> _test_map_cat _ =
>   testName "map(f)(cat(x,y)) == cat(map(f)(x),map(f)(y))" $
>   \f x y -> eq (map f (cat x y)) (cat (map f x) (map f y))

</p></div>
</div>

$\map(f)$ respects $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$. For all $a \in A$ and $x \in \lists{A}$, we have $$\map(f)(\snoc(a,x)) = \snoc(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\nil)) \\
 & = & \map(f)(\cons(a,\nil)) \\
 & = & \cons(f(a),\map(f)(\nil)) \\
 & = & \cons(f(a),\nil) \\
 & = & \snoc(f(a),\nil) \\
 & = & \snoc(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $f$ and $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\snoc(a,\cons(b,x))) \\
 & = & \map(f)(\cons(b,\snoc(a,x))) \\
 & = & \cons(f(b),\map(f)(\snoc(a,x))) \\
 & = & \cons(f(b),\snoc(f(a),\map(f)(x))) \\
 & = & \snoc(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \snoc(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_snoc :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> a -> t a -> Bool)
> _test_map_snoc _ =
>   testName "map(f)(snoc(a,x)) == snoc(f(a),map(f)(x))" $
>   \f a x -> eq (map f (snoc a x)) (snoc (f a) (map f x))

</p></div>
</div>

$\map(f)$ respects $\rev$.

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
 & = & \map(f)(\snoc(a,\rev(x))) \\
 & = & \snoc(f(a),\map(f)(\rev(x))) \\
 & = & \snoc(f(a),\rev(\map(f)(x))) \\
 & = & \rev(\cons(f(a),\map(f)(x)) \\
 & = & \rev(\map(f)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_rev :: (List t, Equal (t a))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_map_rev _ =
>   testName "map(f)(rev(x)) == rev(map(f)(x))" $
>   \f x -> eq (map f (rev x)) (rev (map f x))

</p></div>
</div>

(@@@)

$\map(f)$ interacts with $\at$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with a map $f : A \rightarrow B$ and $x \in \lists{A}$. Then we have $$\at(\map(f)(x),k) = \upair(\id,f)(\at(x,k)).$$
</p></div>

<div class="proof"><p>
There are two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\nil),k) \\
 & = & \at(\nil,k) \\
 & = & \lft(\ast) \\
 & = & \lft(\id(\ast)) \\
 & = & \upair(\id,f)(\lft(\ast)) \\
 & = & \upair(\id,f)(\at(\nil,k))
\end{eqnarray*}$$
as claimed. Suppose instead that $x = \cons(a,y)$. We now proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\zero) \\
 & = & \at(\cons(f(a),\map(f)(y)),\zero) \\
 & = & \rgt(f(a)) \\
 & = & \upair(\id,f)(\rgt(a)) \\
 & = & \upair(\id,f)(\at(\cons(a,y),\zero))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $y$ for some $k$. Now
$$\begin{eqnarray*}
 &   & \at(\map(f)(\cons(a,y)),\next(k)) \\
 & = & \at(\cons(f(a),\map(f)(y)),\next(k)) \\
 & = & \at(\map(f)(y),k) \\
 & = & \upair(\id,f)(\at(y,k)) \\
 & = & \upair(\id,f)(\at(\cons(a,y),\next(k)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_map_at :: (List t, Equal (t a), Natural n, Equal n, Equal a)
>   => t a -> n -> Test ((a -> a) -> t a -> n -> Bool)
> _test_map_at _ _ =
>   testName "at(map(f)(x),k) == upair(id,f)(at(x,k))" $
>   \f x k -> eq (at (map f x) k) (upair id f (at x k))

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

<div class="test"><p>

> _test_map_length :: (List t, Equal (t a), Natural n, Equal n, Equal a)
>   => t a -> n -> Test ((a -> a) -> t a -> Bool)
> _test_map_length _ k =
>   testName "length(map(f)(x)) == length(x)" $
>   \f x -> eq (length (map f x)) ((length x) `withTypeOf` k)

</p></div>
</div>


Testing
-------

Suite:

> _test_map ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   , TypeName n, Show n, Equal n, Natural n, Arbitrary n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_map t n maxSize numCases = do
>   testLabel ("map: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_map_nil t)
>   runTest args (_test_map_cons t)
>   runTest args (_test_map_id t)
>   runTest args (_test_map_compose t)
>   runTest args (_test_map_tail t)
>   runTest args (_test_map_cat t)
>   runTest args (_test_map_snoc t)
>   runTest args (_test_map_rev t)
>   runTest args (_test_map_at t n)
>   runTest args (_test_map_length t n)

Main:

> main_map :: IO ()
> main_map = do
>   _test_map (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_map (nil :: ConsList Unary) (zero :: Unary) 20 100
