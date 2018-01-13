---
title: UnfoldN
author: nbloomf
date: 2017-05-03
tags: arithmetic-made-difficult, literate-haskell
slug: unfoldn
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module UnfoldN
>   ( unfoldN, tacunfoldN, _test_unfoldN, main_unfoldN
>   ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Cat
> import Map

So far we've developed a few functions that operate on lists. But we don't have a convenient programmatic way to *construct* lists out of nothing -- we'll remedy this today with a function called $\unfoldN{\ast}$. From the name, it sounds like unfold should be the "opposite" (or *dual*) of a fold. But the full story is a little more complicated than this; the true opposite to fold doesn't operate on lists at all, but on *streams* (which we'll get to later). Roughly speaking, $\lists{A}$ is an initial algebra, elements of $\lists{A}$ are required to be "finite", and $\foldr{\ast}{\ast}$ condenses a $\lists{A}$ element to a single item. Streams, in contrast, are required to be "infinite" and collectively form a *terminal algebra* and their universal map expands a single item to an infinite structure. All that is to say that the $\unfoldN{\ast}$ function we define here is *not* the real dual of $\foldr{\ast}{\ast}$ -- which partly explains why it is so complicated looking.

So what will $\unfoldN{\ast}$ do? Roughly speaking, we'd like to be able to build up interesting lists of arbitrary size using a small amount of initial data. For example, here is a version of the signature for Haskell's standard ``unfoldr`` function.

```haskell
unfoldr :: (a -> Maybe (a,b)) -> a -> [b]
```

This function takes a seed value ``a`` and a map that takes an ``a`` and returns either ``Nothing`` or a pair ``(a,b)``, and returns a ``[b]``. We can reasonably infer that this function applies the map to the seed, and if that value is ``Nothing``, returns ``[]``, and if the value is an ``(a,b)``, make that ``b`` the head of our list and repeat with the new seed.

There is a problem with translating this type to $\lists{A}$, though. It has to do with the essential finiteness of lists. What happens if the map argument never returns ``Nothing``? Then ``unfoldr`` will happily generate an infinite list.

How can we fix this? One strategy would be to impose some kind of constraint on the map so that it must eventually return a ``Nothing``. That may well be possible, but my hunch is that it would make reasoning about unfolds complicated -- we'd have to prove that a given map satisfies the constraint before using it.

Another strategy -- and the one we will take -- is to give unfold a natural number argument that acts as a countdown timer. If it reaches $\zero$, we're done. (This also explains the ``N`` in $\unfoldN{\ast}$.) This strategy also makes it possible to define $\unfoldN{\ast}$ using bailout recursion on $\nats$.

Before defining $\unfoldN{\ast}$, we need a helper operator, $\tacunfoldN{\ast}$, analogous to $\revcat$. "tac" is a bad pun on "reverse cat" -- since that's kind of what this operator does.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, and let $f : A \rightarrow 1 + (A \times B)$. There is a unique function $$\Theta : \lists{B} \times \nats \times A \rightarrow \lists{B}$$ such that for all $a \in A$, $x \in \lists{A}$, and $n \in \nats$, we have $$\Theta(x,\zero,a) = x$$ and
$$\Theta(x,\next(n),a) = \left\{\begin{array}{ll}
 x & \mathrm{if}\ f(a) = \lft(\ast) \\
 \Theta(\snoc(b,x),n,c) & \mathrm{if}\ f(a) = \rgt((c,b)).
\end{array}\right.$$
We denote this unique map $\tacunfoldN{f}$.
</p></div>

<div class="proof"><p>
We define $\varphi : A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(a,x) = x,$$ $\beta : \nats \times (A \times \lists{B}) \rightarrow \bool$ by $$\beta(n,(a,x)) = \isLft(f(a)),$$ $\psi : \nats \times (A \times \lists{B}) \rightarrow \lists{B}$ by $$\psi(n,(a,x)) = x,$$ and $\omega : \nats \times (A \times \lists{B}) \rightarrow A \times \lists{B}$ by
$$\omega(n,(a,x)) = \left\{\begin{array}{ll}
 (a,x) & \mathrm{if}\ f(a) = \lft(\ast) \\
 (c,\snoc(b,x)) & \mathrm{if}\ f(a) = \rgt((c,b)).
\end{array}\right.$$
Finally, define $$\tacunfoldN{f}(x,n,a) = \bailrec{\varphi}{\beta}{\psi}{\omega}(n,(a,x)).$$ For brevity, in this proof we let $\Omega = \bailrec{\varphi}{\beta}{\psi}{\omega}$.

First we show that $\tacunfoldN{f}$ has the desired properties. To this end, note that
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(x,\zero,a) \\
 & = & \Omega(\zero,(a,x)) \\
 & = & \varphi(a,x) \\
 & = & x.
\end{eqnarray*}$$
Now suppose $f(a) = \lft(\ast)$; then
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(x,\next(n),a) \\
 & = & \Omega(\next(n),(a,x)) \\
 & = & \bif{\beta(a,x)}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \bif{\isLft(f(a))}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \bif{\btrue}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \psi(a,x) \\
 & = & x
\end{eqnarray*}$$
as needed. Suppose instead that $f(a) = \rgt(c,b)$. Then
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(x,\next(n),a) \\
 & = & \Omega(\next(n),(a,x)) \\
 & = & \bif{\beta(a,x)}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \bif{\isLft(f(a))}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \bif{\bfalse}{\psi(a,x)}{\Omega(n,\omega(n,(a,x)))} \\
 & = & \Omega(n,(c,\snoc(b,x))) \\
 & = & \tacunfoldN{f}(\snoc(b,x),n,c)
\end{eqnarray*}$$
as needed.

To see uniqueness, suppose now that $\Psi : \lists{B} \times \nats \times A \rightarrow \lists{B}$ has these properties. We show that $\Psi = \tacunfoldN{f}$ by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \Psi(x,\zero,a) \\
 & = & x \\
 & = & \tacunfoldN{f}(x,\zero,a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\Psi(x,n,a) = \tacunfoldN{f}(x,n,a)$ for all $x$ and $a$ for some $n$. Let $a \in A$. If $f(a) = \lft(\ast)$, then
$$\begin{eqnarray*}
 &   & \Psi(x,\next(n),a) \\
 & = & x \\
 & = & \tacunfoldN{f}(x,\next(n),a)
\end{eqnarray*}$$
as needed. If $f(a) = \rgt((c,b))$, then
$$\begin{eqnarray*}
 &   & \Psi(x,\next(n),a) \\
 & = & \Psi(\snoc(b,x),n,c) \\
 & = & \tacunfoldN{f}(\snoc(b,x),n,c) \\
 & = & \tacunfoldN{f}(x,\next(n),a)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

We can implement $\tacunfoldN{f}$ using the definition from the proof, or by pattern matching using the universal property.

> tacunfoldN', tacunfoldN
>   :: (List t, Natural n)
>   => (a -> Either () (a,b)) -> t b -> n -> a -> t b
> 
> tacunfoldN' f x n a = bailoutRec phi beta psi omega n (a,x)
>   where
>     phi (a,x) = x
>     beta n (a,x) = isLft (f a)
>     psi n (a,x) = x
>     omega n (a,x) = case f a of
>       Left () -> (a,x)
>       Right (c,b) -> (c, snoc b x)
> 
> 
> tacunfoldN f x n a = case unnext n of
>   Left () -> x
>   Right k -> case f a of
>     Left () -> x
>     Right (c,b) -> tacunfoldN f (snoc b x) k c

We should test that these two implementations agree.

> _test_tacunfoldN_equiv :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> t a -> n -> a -> Bool)
> _test_tacunfoldN_equiv _ _ =
>   testName "tacunfoldN(x,n,a) == tacunfoldN'(x,n,a)" $
>   \f x n a -> eq (tacunfoldN f x n a) (tacunfoldN' f x n a)

And while we're at it, test that $\tacunfoldN{f}$ does satisfy the universal property.

> _test_tacunfoldN_zero :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> t a -> a -> Bool)
> _test_tacunfoldN_zero _ k =
>   testName "tacunfoldN(x,zero,a) == x" $
>   \f x a -> eq (tacunfoldN f x (zero `withTypeOf` k) a) x
> 
> 
> _test_tacunfoldN_next :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> t a -> n -> a -> Bool)
> _test_tacunfoldN_next _ _ =
>   testName "tacunfoldN(x,next(n),a) == if(isLft(f(a)),x,tacunfoldN(snoc(b,x),n,c))" $
>   \f x n a -> case f a of
>     Left () -> eq (tacunfoldN f x (next n) a) x
>     Right (c,b) -> eq (tacunfoldN f x (next n) a) (tacunfoldN f (snoc b x) n c)

$\tacunfoldN{f}$ interacts with $\cons$.

<div class="result">
<div class="thm"><p>
We have $$\tacunfoldN{f}(\cons(b,x),n,a) = \cons(b,\tacunfoldN{f}(x,n,a)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cons(b,x),\zero,a) \\
 & = & \cons(b,x) \\
 & = & \cons(b,\tacunfoldN{f}(x,\zero,a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$, $b$, and $x$ for some $n$. If $f(a) = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cons(b,x),\next(n),a) \\
 & = & \cons(b,x) \\
 & = & \cons(b,\tacunfoldN{f}(x,n,a))
\end{eqnarray*}$$
as needed, while if $f(a) = \rgt((c,d))$ we have
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cons(b,x),\next(n),a) \\
 & = & \tacunfoldN{f}(\snoc(d,\cons(b,x)),n,c) \\
 & = & \tacunfoldN{f}(\cons(b,\snoc(d,x)),n,c) \\
 & = & \cons(b,\tacunfoldN{f}(\snoc(d,x),n,c)) \\
 & = & \cons(b,\tacunfoldN{f}(x,\next(n),a))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_tacunfoldN_cons :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> t a -> a -> n -> a -> Bool)
> _test_tacunfoldN_cons _ _ =
>   testName "tacunfoldN(cons(b,x),n,a) == cons(b,tacunfoldN(x,n,a))" $
>   \f x b n a -> eq (tacunfoldN f (cons b x) n a) (cons b (tacunfoldN f x n a))

</p></div>
</div>

$\tacunfoldN{f}$ interacts with $\cat$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow 1 + (A \times B)$. For all $a \in A$, $x,y \in \lists{B}$, and $n \in \nats$, we have $$\tacunfoldN{f}(\cat(x,y),n,a) = \cat(x,\tacunfoldN{f}(y,n,a).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cat(x,y),\zero,a) \\
 & = & \cat(x,y) \\
 & = & \cat(x,\tacunfoldN{f}(y,\zero,a))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$, $y$, and $a$ for some $n$. Now let $a \in A$; we have two possibilities for $f(a)$. If $f(a) = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cat(x,y),\next(n),a) \\
 & = & \cat(x,y) \\
 & = & \cat(x,\tacunfoldN{f}(y,\next(n),a))
\end{eqnarray*}$$
as needed. Suppose instead that $f(a) = \rgt((c,d))$. Now
$$\begin{eqnarray*}
 &   & \tacunfoldN{f}(\cat(x,y),\next(n),a) \\
 & = & \tacunfoldN{f}(\snoc(d,\cat(x,y)),n,c) \\
 & = & \tacunfoldN{f}(\cat(x,\snoc(d,y)),n,c) \\
 & = & \cat(x,\tacunfoldN{f}(\snoc(d,y),n,c) \\
 & = & \cat(x,\tacunfoldN{f}(y,\next(n),a)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_tacunfoldN_cat :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> t a -> t a -> n -> a -> Bool)
> _test_tacunfoldN_cat _ _ =
>   testName "tacunfoldN(cat(x,y),n,a) == cat(x,tacunfoldN(y,n,a))" $
>   \f x y n a -> eq (tacunfoldN f (cat x y) n a) (cat x (tacunfoldN f y n a))

</p></div>
</div>

Now we can define $\unfoldN{\ast}$ in terms of $\tacunfoldN{\ast}$.

<div class="result">
<div class="dfn"><p>
Let $A$ and $B$ be sets, with $f : A \rightarrow 1 + (A \times B)$. we define $\unfoldN{f} : \nats \times A \rightarrow \lists{B}$ by $$\unfoldN{f}(n,a) = \tacunfoldN{f}(\nil,n,a).$$

In Haskell:

> unfoldN
>   :: (List t, Natural n)
>   => (a -> Either () (a,b)) -> n -> a -> t b
> unfoldN f = tacunfoldN f nil

</p></div>
</div>

And $\unfoldN{\ast}$ can be characterized as the unique solution of a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow 1 + (A \times B)$. Then $\unfoldN{f}$ is the unique map $g : \nats \times A \rightarrow B$ such that the following hold for all $a \in A$ and $n \in \nats$.
$$\left\{\begin{array}{l}
 g(\zero,a) = \nil \\
 g(\next(n),a) = \left\{\begin{array}{ll}
  \nil & \mathrm{if}\ f(a) = \lft(\ast) \\
  \cons(b,g(n,c)) & \mathrm{if}\ f(a) = \rgt((c,b)). 
\end{array}\right.
\end{array}\right.$$
</p></div>

<div class="proof"><p>
To see that $\unfoldN{\ast}$ satisfies the first equation, note that
$$\begin{eqnarray*}
 &   & \unfoldN{f}(\zero,a) \\
 & = & \tacunfoldN{f}(\nil,\zero,a) \\
 & = & \nil
\end{eqnarray*}$$
as needed. We show the second by induction on $n$. For the base case $n = \zero$, if $a \in A$ and $f(a) = \lft(\ast)$ we have
$$\begin{eqnarray*}
 &   & \unfoldN{f}(\next(\zero),a) \\
 & = & \tacunfoldN{f}(\nil,\next(\zero),a) \\
 & = & \nil
\end{eqnarray*}$$
as needed, and if $f(a) = \rgt((c,b))$ we have
$$\begin{eqnarray*}
 &   & \unfoldN{f}(\next(\zero),a) \\
 & = & \tacunfoldN{f}(\nil,\next(\zero),a) \\
 & = & \tacunfoldN{f}(\snoc(b,\nil),\zero,c) \\
 & = & \snoc(b,\nil) \\
 & = & \cons(b,\nil) \\
 & = & \cons(b,\tacunfoldN{f}(\nil,\zero,a) \\
 & = & \cons(b,\unfoldN{f}(\zero,a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $n$. Let $a \in A$. If $f(a) = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & \unfoldN{f}(\next(n),a) \\
 & = & \tacunfoldN(\nil,\next(n),a) \\
 & = & \nil
\end{eqnarray*}$$
as needed, while if $f(a) = \rgt((c,b))$ we have
$$\begin{eqnarray*}
 &   & \unfoldN{f}(\next(n),a) \\
 & = & \tacunfoldN{f}(\nil,\next(n),a) \\
 & = & \tacunfoldN{f}(\snoc(b,\nil),n,c) \\
 & = & \tacunfoldN{f}(\cons(b,\nil),n,c) \\
 & = & \cons(b,\tacunfoldN{f}(\nil,n,c)) \\
 & = & \cons(b,\unfoldN{f}(n,c))
\end{eqnarray*}$$
as needed.

To see that $\unfoldN{f}$ is unique we again induct on $n$. Suppose $\Psi$ is another solution. For the base case $n = \zero$ note that
$$\begin{eqnarray*}
 &   & \Psi(\zero,a) \\
 & = & \nil \\
 & = & \unfoldN{f}(\zero,a)
\end{eqnarray*}$$
as needed. For the inductive step, suppose we have $\Psi(n,a) = \unfoldN{f}(n,a)$ for all $a$ for some $n$, and let $a \in A$. If $f(a) = \lft(\ast)$, then
$$\begin{eqnarray*}
 &   & \Psi(\next(n),a) \\
 & = & \nil \\
 & = & \unfoldN{f}(\next(n),a)
\end{eqnarray*}$$
as needed, while if $f(a) = \rgt((c,b))$ we have
$$\begin{eqnarray*}
 &   & \Psi(\next(n),a) \\
 & = & \cons(b,\Psi(n,c)) \\
 & = & \cons(b,\unfoldN{f}(n,c)) \\
 & = & \unfoldN{f}(\next(n),a)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_unfoldN_zero :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> a -> Bool)
> _test_unfoldN_zero t k =
>   testName "unfoldN(zero,a) == nil" $
>   \f a -> eq (unfoldN f (zero `withTypeOf` k) a) (nil `withTypeOf` t)
> 
> 
> _test_unfoldN_next :: (List t, Equal (t a), Natural n)
>   => t a -> n -> Test ((a -> Either () (a,a)) -> n -> a -> Bool)
> _test_unfoldN_next t _ =
>   testName "unfoldN(next(n),a) == if(isLft(f(a)),nil,cons(b,unfoldN(n,c)))" $
>   \f n a -> case f a of
>     Left ()     -> eq (unfoldN f (next n) a) (nil `withTypeOf` t)
>     Right (c,b) -> eq (unfoldN f (next n) a) ((cons b (unfoldN f n c)) `withTypeOf` t)

</p></div>
</div>


Testing
-------

Suite:

> _test_unfoldN ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   , TypeName n, Equal n, Show n, Arbitrary n, Natural n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_unfoldN t n maxSize numCases = do
>   testLabel ("unfoldN: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_tacunfoldN_equiv t n)
>   runTest args (_test_tacunfoldN_zero t n)
>   runTest args (_test_tacunfoldN_next t n)
>   runTest args (_test_tacunfoldN_cat t n)
>   runTest args (_test_tacunfoldN_cons t n)
> 
>   runTest args (_test_unfoldN_zero t n)
>   runTest args (_test_unfoldN_next t n)

Main:

> main_unfoldN :: IO ()
> main_unfoldN = do
>   _test_unfoldN (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_unfoldN (nil :: ConsList Unary) (zero :: Unary) 20 100
