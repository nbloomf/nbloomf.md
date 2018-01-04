---
title: Range
author: nbloomf
date: 2017-05-05
tags: arithmetic-made-difficult, literate-haskell
slug: range
---

> module Range
>   ( range, _test_range, main_range
>   ) where
> 
> import Prelude ()
> import Booleans
> import DisjointUnions
> import NaturalNumbers
> import Plus
> import Lists
> import Snoc
> import Reverse
> import Cat
> import Length
> import At
> import Map
> import UnfoldN

For our first application of $\unfoldN$ we'll define a function, $\range$, that constructs lists of natural numbers. There are a few ways to do this. We could take an argument $n$ and construct the list of natural numbers from $\zero$ to $n$, but this is too specialized. We could instead take *two* arguments $a$ and $b$ and construct the list of natural numbers from $a$ to $b$, but we'll have to check whether or not the arguments are in order. A third option -- and the one we'll take -- is to take two arguments $a$ and $b$, and construct the list of the first $b$ natural numbers starting from $a$.

<div class="result">
<div class="defn"><p>
Define $f : \nats \rightarrow \ast + \nats \times \nats$ by $$f(k) = (\next(k),k).$$ We then define $\range : \nats \times \nats \rightarrow \lists{\nats}$ by $$\range(a,b) = \unfoldN(f,b,a).$$

In Haskell:

> range :: (List t, Natural n, Equal n) => n -> n -> t n
> range a b = unfoldN f b a
>   where f k = rgt (next k, k)

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

$\range$ interacts with $\next$ in its second argument:

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

$\range$ interacts with $\nplus$ in its second argument:

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

$\range$ interacts with $\next$ in its first argument:

<div class="result">
<div class="thm"><p>
For all $a,b \in \nats$ we have $$\range(\next(a),b) = \map(\next)(\range(a,b)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $b$. For the base case $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \range(\next(a),b) \\
 & = & \range(\next(a),\zero) \\
 & = & \nil \\
 & = & \map(\next)(\nil) \\
 & = & \map(\next)(\range(a,\zero)) \\
 & = & \map(\next)(\range(a,b))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $b$. Now
$$\begin{eqnarray*}
 &   & \range(\next(a),\next(b)) \\
 & = & \cons(\next(a),\range(\next(\next(a)),b)) \\
 & = & \cons(\next(a),\map(\next)(\range(\next(a),b))) \\
 & = & \map(\next)(\cons(a,\range(\next(a),b))) \\
 & = & \map(\next)(\range(a,\next(b)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\range$ interacts with $\nplus$ in its first argument. In this theorem we use a bit of new notation. When a function argument is replaced by a dash, we implicitly mean lambda-abstraction. That is, if $f$ is a function, then $f(-)$ is short for $\lambda x. f(x)$.

<div class="result">
<div class="thm"><p>
If $a,b,c \in \nats$, we have $$\range(\nplus(a,b),c) = \map(\nplus(a,-))(\range(b,c)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case $a = \zero$ note that $\nplus(a,-) = \id$, since for all $b \in \nats$ we have $$\nplus(\zero,-)(b) = \nplus(\zero,b) = b.$$ Thus
$$\begin{eqnarray*}
 &   & \range(\nplus(a,b),c) \\
 & = & \range(\nplus(\zero,b),c) \\
 & = & \range(b,c) \\
 & = & \map(\id)(\range(b,c)) \\
 & = & \map(\nplus(\zero,-))(\range(b,c)) \\
 & = & \map(\nplus(a,-))(\range(b,c))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $a$. Now
$$\begin{eqnarray*}
 &   & \range(\nplus(\next(a),b),c) \\
 & = & \range(\next(\nplus(a,b)),c) \\
 & = & \map(\next)(\range(\nplus(a,b),c)) \\
 & = & \map(\next)(\map(\nplus(a,-))(\range(b,c))) \\
 & = & (\map(\next) \circ \map(\nplus(a,-)))(\range(b,c)) \\
 & = & \map(\next(\nplus(a,-)))(\range(b,c)) \\
 & = & \map(\nplus(\next(a),-))(\range(b,c))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\range$.

> _test_range_next_cons :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_next_cons t =
>   testName "range(a,next(b)) == cons(a,range(next(a),b))" $
>   \a b -> let
>     x = (range a (next b)) `withTypeOf` t
>     y = (cons a (range (next a) b))
>   in
>     eq x y
> 
> 
> _test_range_next_snoc :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_next_snoc t =
>   testName "range(a,next(b)) == snoc(plus(a,b),range(a,b))" $
>   \a b -> let
>     x = (range a (next b)) `withTypeOf` t
>     y = (snoc (plus a b) (range a b))
>   in
>     eq x y
> 
> 
> _test_range_plus_right :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> n -> Bool)
> _test_range_plus_right t =
>   testName "range(a,plus(b,c)) == cat(range(a,b),range(plus(a,b),c))" $
>   \a b c -> let
>     x = (range a (plus b c)) `withTypeOf` t
>     y = (cat (range a b) (range (plus a b) c))
>   in
>     eq x y
> 
> 
> _test_range_next_left :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> Bool)
> _test_range_next_left t =
>   testName "range(next(a),b) == map(next,range(a,b))" $
>   \a b -> let
>     x = (range (next a) b) `withTypeOf` t
>     y = (map next (range a b))
>   in
>     eq x y
> 
> 
> _test_range_plus_left :: (List t, Natural n, Equal (t n), Equal n)
>   => t n -> Test (n -> n -> n -> Bool)
> _test_range_plus_left t =
>   testName "range(plus(a,b),c) == map(plus(a,-),range(b,c))" $
>   \a b c -> let
>     x = (range (plus a b) c) `withTypeOf` t
>     y = (map (plus a) (range b c))
>   in
>     eq x y

And the suite:

> _test_range ::
>   ( TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t n), List t, Equal (t n), Show (t n), Arbitrary (t n)
>   ) => t n -> Int -> Int -> IO ()
> _test_range t maxSize numCases = do
>   testLabel ("range: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_range_next_cons t)
>   runTest args (_test_range_next_snoc t)
>   runTest args (_test_range_plus_right t)
>   runTest args (_test_range_next_left t)
>   runTest args (_test_range_plus_left t)

And ``main``:

> main_range :: IO ()
> main_range = do
>   _test_range (nil :: ConsList Unary) 20 100
