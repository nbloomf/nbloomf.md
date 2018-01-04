---
title: UnfoldN
author: nbloomf
date: 2017-05-03
tags: arithmetic-made-difficult, literate-haskell
slug: unfoldn
---

> module UnfoldN
>   ( unfoldN, tacunfoldN, _test_unfoldN, main_unfoldN
>   ) where
> 
> import Prelude ()
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

(@@@)

So far we've developed a few functions that operate on lists. But we don't have a convenient programmatic way to *construct* lists out of nothing -- we'll remedy this today with a function called $\unfoldN{\ast}$. From the name, it sounds like unfold should be the "opposite" (or *dual*) of a fold. But the full story is a little more complicated than this; the true opposite to fold doesn't operate on lists at all, but on *streams* (which we'll get to later). Roughly speaking, $\lists{A}$ is an initial algebra, elements of $\lists{A}$ are required to be "finite", and $\foldr{\ast}{\ast}$ condenses a $\lists{A}$ element to a single item. Streams, in contrast, are required to be "infinite" and collectively form a *terminal algebra* and their universal map expands a single item to an infinite structure. All that is to say that the $\unfoldN{\ast}$ function we define here is *not* the real dual of $\foldr{\ast}{\ast}$ -- which partly explains why it is so complicated looking.

So what will $\unfoldN{\ast}$ do? Roughly speaking, we'd like to be able to build up interesting lists of arbitrary size using a small amount of initial data. For example, here is a version of the signature for Haskell's standard ``unfoldr`` function.

```haskell
unfoldr :: (a -> Maybe (a,b)) -> a -> [b]
```

This function takes a seed value ``a`` and a map that takes an ``a`` and returns either ``Nothing`` or a pair ``(a,b)``, and returns a ``[b]``. We can reasonably infer that this function applies the map to the seed, and if that value is ``Nothing``, returns ``[]``, and if the value is an ``(a,b)``, make that ``b`` the head of our list and repeat with the new seed.

There is a problem with translating this type to $\lists{A}$, though. It has to do with the essential finiteness of lists. What happens if the map argument never returns ``Nothing``? Then ``unfoldr`` will happily generate an infinite list.

How can we fix this? One strategy would be to impose some kind of constraint on the map so that it must eventually return a ``Nothing``. That may well be possible, but my hunch is that it would make reasoning about unfolds complicated -- we'd have to prove that a given map satisfies the constraint before using it.

Another strategy -- and the one we will take -- is to give unfold a natural number argument that acts as a countdown timer. If it reaches $\zero$, we're done. (This also explains the ``N`` in $\unfoldN{\ast}$.) This strategy also makes it possible to define $\unfoldN{\ast}$ using bailout recursion on $\nats$.

Before defining $\unfoldN{\ast}$, we need a helper operator analogous to $\revcat$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, and let $f : A \rightarrow 1 + (A \times B)$. There is a unique function $$\Theta : \lists{B} \times \nats \times A \rightarrow \lists{B}$$ such that for all $a \in A$, $x \in \lists{A}$, and $n \in \nats$, we have $$\Theta(x,\zero,a) = x$$ and
$$\Theta(x,\next(n),a) = \left\{\begin{array}{ll}
 x & \mathrm{if}\ f(a) = \lft(\ast) \\
 \Theta(\snoc(b,x),n,c) & \mathrm{if}\ f(a) = \rgt((c,b)).
\end{array}\right.$$
We denote this unique map $\tacunfoldN{f}$.
</p>

<div class="proof"><p>
We define $\varphi : A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(a,x) = x,$$ $\beta : \nats \times (A \times \lists{B}) \rightarrow \bool$ by $$\beta(n,(a,x)) = \isLft(f(a)),$$ $\psi : \nats \times (A \times \lists{B}) \rightarrow \lists{B}$ by $$\psi(n,(a,x)) = x,$$ and $\omega : \nats \times (A \times \lists{B}) \rightarrow A \times \lists{B}$ by
$$\omega(n,(a,x)) = \left\{\begin{array}{ll}
 (a,x) & \mathrm{if}\ f(a) = \lft(\ast) \\
 (c,\snoc(b,x)) & \mathrm{if}\ f(a) = \rgt((c,b)).
\end{array}\right.$$
Finally, define $$\tacunfoldN{f}(x,n,a) = \bailoutRec{\varphi}{\beta}{\psi}{\omega}(n,(a,x)).$$ For brevity, in this proof we let $\Omega = \bailoutRec{\varphi}{\beta}{\psi}{\omega}$.

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

(@@@)

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, and let $f : A \rightarrow 1 + (A \times B)$. There is a unique map $\Omega : \nats \times A \rightarrow \lists{B}$ such that $$\Omega(\zero,a) = \nil$$ and
$$\Omega(\next(n),a) = \left\{\begin{array}{ll}
 \nil & \mathrm{if}\ f(a) = \lft(\ast) \\
 \cons(b,\Theta(n,c)) & \mathrm{if}\ f(a) = \rgt((b,c)).
\end{array}\right.$$
We denote this map $\unfoldN{f}$.
</p></div>

<div class="proof"><p>
Define $\varphi : A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(a,x) = \rev(x),$$ $\beta : \nats \times (A \times \lists{B}) \rightarrow \bool$ by $$\beta(k,(a,x)) = \bif{\isLft(f(a))}{\btrue}{\bfalse},$$ $\psi : \nats \times (A \times \lists{B}) \rightarrow \lists{B}$ by $$\psi(k,(a,x)) = \rev(x),$$ and $\omega : \nats \times (A \times \lists{B}) \rightarrow A \times \lists{B}$ by $$\omega(k,(a,x)) = \left\{\begin{array}{ll} (a,x) & \mathrm{if}\ f(a) = \lft(\ast) \\ (d,\cons(b,x)) & \mathrm{if}\ f(a) = \rgt((d,b)). \end{array}\right.$$ Now let $\Omega : \nats \times A \rightarrow \lists{B}$ be given by $$\Omega(k,a) = \bailrec{\varphi}{\beta}{\psi}{\omega}(k,(a,\nil)).$$

To see that $\Omega$ has the claimed properties, note that
$$\begin{eqnarray*}
 &   & \Omega(\zero,a) \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(\zero,(a,\nil)) \\
 & = & \varphi(a,\nil) \\
 & = & \rev(\nil) \\
 & = & \nil,
\end{eqnarray*}$$
and if $f(a) = \lft(\ast)$, we have
$$\begin{eqnarray*}
 &   & \Omega(\next(n),a) \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(\next(n),(a,\nil)) \\
 & = & \bif{\beta(n,(a,\nil))}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \bif{\bif{\isLft(f(a))}{\btrue}{\bfalse}}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \bif{\btrue}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \psi(n,(a,\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil,
\end{eqnarray*}$$
and if $f(a) = \rgt((b,c))$, we have
$$\begin{eqnarray*}
 &   & \Omega(\next(n),a) \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(\next(n),(a,\nil)) \\
 & = & \bif{\beta(n,(a,\nil))}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \bif{\bif{\isLft(f(a))}{\btrue}{\bfalse}}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \bif{\bfalse}{\psi(n,(a,\nil))}{\bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil)))} \\
 & = & \bailrec{\varphi}{\beta}{\psi}{\omega}(n,\omega(n,(a,\nil))) \\
 & = & 
\end{eqnarray*}$$
</p></div>
</div>

We won't prove many general properties of $\unfoldN$ here; instead we will define more specific functions in terms of $\unfoldN$ and prove properties about them.

One lemma will be useful though.

<div class="result">
<div class="thm"><p>
For all $k \in \nats$, $a \in A$, and $x \in \lists{B}$, we have $$\Theta(k,(a,x)) = \cat(\rev(x),\unfoldN(f,k,a)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \Theta(k,(a,x) \\
 & = & \Theta(\zero,(a,x)) \\
 & = & \varphi(a,x) \\
 & = & \rev(x) \\
 & = & \cat(\rev(x),\nil) \\
 & = & \cat(\rev(x),\rev(\nil)) \\
 & = & \cat(\rev(x),\Theta(\zero,(a,\nil))) \\
 & = & \cat(\rev(x),\unfoldN(f,\zero,a)) \\
 & = & \cat(\rev(x),\unfoldN(f,k,a))
\end{eqnarray*}$$
as needed.

For the inductive step, suppose the equality holds for all $a$ and $x$ for some $k$. Now let $a \in A$. We consider two possibilities for $f(a)$; either $f(a) = \ast$ or $f(a) \neq \ast$. If $f(a) = \ast$, then we have
$$\begin{eqnarray*}
 &   & \Theta(\next(k),(a,x)) \\
 & = & \psi(k,(a,x)) \\
 & = & \rev(x) \\
 & = & \cat(\rev(x),\nil) \\
 & = & \cat(\rev(x),\rev(\nil)) \\
 & = & \cat(\rev(x),\psi(k,(a,\nil))) \\
 & = & \cat(\rev(x),\Theta(\next(k),(a,\nil))) \\
 & = & \cat(\rev(x),\unfoldN(f,\next(k),a)) \\
\end{eqnarray*}$$
as needed.

Finally, suppose we have $f(a) = (d,e)$ with $d \in A$ and $e \in B$. Using the inductive hypothesis twice we have
$$\begin{eqnarray*}
 &   & \Theta(\next(k),(a,x)) \\
 & = & \Theta(k,(d,\cons(e,x)) \\
 & = & \cat(\rev(\cons(e,x)),\unfoldN(f,k,d)) \\
 & = & \cat(\rev(\cons(e,x)),\unfoldN(f,k,d)) \\
 & = & \cat(\snoc(e,\rev(x)),\unfoldN(f,k,d)) \\
 & = & \cat(\rev(x),\cons(e,\unfoldN(f,k,d))) \\
 & = & \cat(\rev(x),\cat(\cons(e,\nil),\unfoldN(f,k,d))) \\
 & = & \cat(\rev(x),\cat(\rev(\cons(e,\nil)),\unfoldN(f,k,d))) \\
 & = & \cat(\rev(x),\Theta(k,(d,\cons(e,\nil)))) \\
 & = & \cat(\rev(x),\Theta(k,\omega(f)(k,(a,\nil)))) \\
 & = & \cat(\rev(x),\Theta(\next(k),(a,\nil))) \\
 & = & \cat(\rev(x),\unfoldN(f,\next(k),a))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Implementation
--------------

We can implement $\unfoldN$ in terms of bailout recursion as in the definition.

> unfoldN' :: (List t, Natural n)
>   => (a -> Maybe (a,b)) -> n -> a -> t b
> unfoldN' f k a = bailoutRec phi (beta f) psi (omega f) k (a,nil)
>   where
>     phi       (_,x) = rev x
>
>     beta  g _ (b,y) = case g b of
>       Nothing -> True
>       Just _  -> False
>
>     psi     _ (_,x) = rev x
>
>     omega g _ (b,y) = case g b of
>       Nothing    -> (b,y)
>       Just (c,d) -> (c, cons d y)

However, unrolling the definition yields a more intuitive implementation.

<div class="result">
<div class="thm"><p>
For all $f$, $k$, and $a$, we have the following.

1. $\unfoldN(f,\zero,a) = \nil$.
2. $$\unfoldN(f,\next(k),a) = \left\{\begin{array}{ll} \nil & \mathrm{if}\ f(a) = \ast \\ \cons(b,\unfoldN(f,k,c)) & \mathrm{if}\ f(a) = (c,b). \end{array}\right.$$
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \unfoldN(f,\zero,a) \\
 & = & \Theta(\zero,(a,\nil)) \\
 & = & \varphi(a,\nil) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. If $f(a) = \ast$, then
$$\begin{eqnarray*}
 &   & \unfoldN(f,\next(k),a) \\
 & = & \Theta(\next(k),(a,\nil)) \\
 & = & \psi(k,(a,\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil.
\end{eqnarray*}$$
If $f(a) = (c,b)$, then
$$\begin{eqnarray*}
 &   & \unfoldN(f,\next(k),a) \\
 & = & \Theta(\next(k),(a,\nil)) \\
 & = & \Theta(k,\omega(f)(a,\nil)) \\
 & = & \Theta(k,(c,\cons(b,\nil))) \\
 & = & \cat(\rev(\cons(b,\nil)),\unfoldN(f,k,c)) \\
 & = & \cat(\cons(b,\nil),\unfoldN(f,k,c)) \\
 & = & \cons(b,\cat(\nil,\unfoldN(f,k,c))) \\
 & = & \cons(b,\unfoldN(f,k,c))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

> unfoldN :: (List t, Natural n)
>   => (a -> Either () (a,b)) -> n -> a -> t b
> unfoldN f n a = case natShape n of
>   Zero   -> nil
>   Next k -> case f a of
>     Left ()     -> nil
>     Right (c,b) -> cons b (unfoldN f k c)


Testing
-------

Suite:

> _test_unfoldN ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   , TypeName n, Equal n, Show n, Arbitrary n, Natural n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_unfoldN t n maxSize numCases = do
>   testLabel ("rev: " ++ typeName t)
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

Main:

> main_unfoldN :: IO ()
> main_unfoldN = do
>   _test_unfoldN (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_unfoldN (nil :: ConsList Unary) (zero :: Unary) 20 100
