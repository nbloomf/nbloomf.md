---
title: UnfoldN
author: nbloomf
date: 2017-05-03
tags: arithmetic-made-difficult, literate-haskell
---

> module UnfoldN
>   ( unfoldN
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
> import Map
> 
> import Test.QuickCheck

So far we've developed a few functions that operate on lists. But we don't have a convenient programmatic way to *construct* lists -- we'll remedy this today with a function called $\unfoldN$. From the name, it sounds like unfold should be the "opposite" (or *dual*) of a fold. But the full story is a little more complicated than this; the true opposite to fold doesn't operate on lists at all, but on *streams* (which we haven't defined). Roughly speaking, $\lists{A}$ is an initial algebra, elements of $\lists{A}$ are required to be "finite", and $\foldr{\ast}{\ast}$ condenses a $\lists{A}$ element to a single item. Streams, in contrast, are required to be "infinite" and collectively form a *terminal algebra* and their universal map expands a single item to an infinite structure. All that is to say that the $\unfoldN$ function we define here is *not* the real dual of $\foldr{\ast}{\ast}$ -- which partly explains why it is so complicated looking.

So what will $\unfoldN$ do? Roughly speaking, we'd like to be able to build up interesting lists of arbitrary size using a small amount of initial data. For example, here is a version of the signature for Haskell's standard ``unfoldr`` function.

```haskell
unfoldr :: (a -> Maybe (a,b)) -> a -> [b]
```

This function takes a seed value ``a`` and a map that takes an ``a`` and returns either ``Nothing`` or a pair ``(a,b)``, and returns a ``[b]``. We can reasonably infer that this function applies the map to the seed, and if that value is ``Nothing``, returns ``[]``, and if the value is an ``(a,b)``, make that ``b`` the head of our list and repeat with the new seed.

There is a problem with translating this type to $\lists{A}$, though. It has to do with the essential finiteness of lists. What happens if the map argument never returns ``Nothing``? Then ``unfoldr`` will happily generate an infinite list.

How can we fix this? One strategy would be to impose some kind of constraint on the map so that it must eventually return a ``Nothing``. That may well be possible, but my hunch is that it would make reasoning about unfolds complicated -- we'd have to prove that a given map satisfies the constraint before using it.

Another strategy -- and the one we will take -- is to give unfold a natural number argument that acts as a countdown timer. If it reaches $\zero$, we're done. (This also explains the ``N`` in $\unfoldN$.) This strategy also makes it possible to define $\unfoldN$ using bailout recursion on $\nats$.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\varphi : A \times \lists{B} \rightarrow \lists{B}$ by $$\varphi(a,x) = \rev(x),$$ $\beta : (\ast + A \times B)^A \rightarrow \nats \times (A \times \lists{B}) \rightarrow \bool$ by $$\beta(f)(k,(a,x)) = \left\{\begin{array}{ll} \btrue & \mathrm{if}\ f(a) = \ast \\ \bfalse & \mathrm{otherwise}, \end{array}\right.$$ $\psi : \nats \times (A \times \lists{B}) \rightarrow \lists{B}$ by $$\psi(k,(a,x)) = \rev(x),$$ and $\omega : (\ast + A \times B)^A \rightarrow \nats \times (A \times \lists{B}) \rightarrow A \times \lists{B}$ by $$\omega(f)(k,(a,x)) = \left\{\begin{array}{ll} (a,x) & \mathrm{if}\ f(a) = \ast \\ (d,\cons(b,x)) & \mathrm{if}\ f(a) = (d,b). \end{array}\right.$$ We then define $$\unfoldN : (\ast + A \times B)^A \times \nats \times A \rightarrow \lists{B}$$ by $$\unfoldN(f,k,a) = \bailrec{\varphi}{\beta(f)}{\psi}{\omega(f)}(k,(a,\nil)).$$

In Haskell:

> unfoldN :: (ListOf t, Natural n)
>   => (a -> Maybe (a,b)) -> n -> a -> t b
> unfoldN f k a = bailoutRec phi (beta f) psi (omega f) k (a,nil)
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

</p></div>
</div>

We let $\Theta = \bailrec{\varphi}{\beta(f)}{\psi}{\omega(f)}$ as in the definition of $\unfoldN$.

Special case:

<div class="result">
<div class="thm"><p>
For all $f$ and $a$, we have $\unfoldN(f,\zero,a) = \nil$.
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \unfoldN(f,\zero,a) \\
 & = & \Theta(\zero,(a,\nil)) \\
 & = & \varphi(a,\nil) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
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
