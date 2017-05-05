---
title: Zip
author: nbloomf
date: 2017-05-06
tags: arithmetic-made-difficult, literate-haskell
---

> module Zip
>   ( zip, zipPad, _test_zip, main_zip, swap, pair, assocL, assocR
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, length, head, tail, map, zip, min, max)
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

> zip' :: (ListOf t) => t a -> t b -> t (a,b)
> zip' = foldr epsilon phi
>   where
>     phi :: (ListOf t) => a -> (t b -> t (a,b)) -> t b -> t (a,b)
>     phi x f z = case listShape z of
>       Nil       -> nil
>       Cons y ys -> cons (x,y) (f ys)
>
>     epsilon :: (ListOf t) => t b -> t (a,b)
>     epsilon _ = nil

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

In Haskell:

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

Define $\assocL : A \times (B \times C) \rightarrow (A \times B) \times C$ by $$\assocL(a,(b,c)) = ((a,b),c).$$

Define $\assocR : (A \times B) \times C \rightarrow A \times (B \times C)$ by $$\assocR((a,b),c) = (a,(b,c)).$$

In Haskell:

> swap :: (a,b) -> (b,a)
> swap (a,b) = (b,a)
> 
> pair :: (a -> u) -> (b -> v) -> (a,b) -> (u,v)
> pair f g (a,b) = (f a, g b)
> 
> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL (a,(b,c)) = ((a,b),c)
> 
> assocR :: ((a,b),c) -> (a,(b,c))
> assocR ((a,b),c) = (a,(b,c))

</p></div>
</div>

Now $\map(\swap) \circ \zip = \zip \circ \swap$:

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
as needed. For the inductive step, suppose the equality holds for all $y \in \lists{B}$ for some $x \in \lists{A}$, and let $a \in A$. Now we consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zip(\cons(a,x),y)) \\
 & = & \map(\swap)(\zip(\cons(a,x),\nil)) \\
 & = & \map(\swap)(\nil) \\
 & = & \nil \\
 & = & \zip(\nil,\cons(a,x)) \\
 & = & \zip(y,\cons(a,x))
\end{eqnarray*}$$
as needed. If $y = \cons(b,z)$, using the induction hypotheses, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zip(\cons(a,x),y)) \\
 & = & \map(\swap)(\zip(\cons(a,x),\cons(b,z))) \\
 & = & \map(\swap)(\cons((a,b),\zip(x,z))) \\
 & = & \cons(\swap(a,b),\map(\swap)(\zip(x,z))) \\
 & = & \cons((b,a),\zip(z,x)) \\
 & = & \zip(\cons(b,z),\cons(a,x)) \\
 & = & \zip(y,\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\map(\pair(f,g)) \circ \zip = \zip \circ \pair(\map(f),\map(g))$:

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
as needed. For the inductive step, suppose the result holds for all $y$ for some $x \in \lists{A}$, and let $a \in A$. We now consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zip(\cons(a,x),y)) \\
 & = & \map(\pair(f,g))(\zip(\cons(a,x),\nil)) \\
 & = & \map(\pair(f,g))(\nil) \\
 & = & \nil \\
 & = & \zip(\map(f)(\cons(a,x)),\nil) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(\nil)) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed. If $y = \cons(b,z)$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zip(\cons(a,x),y)) \\
 & = & \map(\pair(f,g))(\zip(\cons(a,x),\cons(b,z))) \\
 & = & \map(\pair(f,g))(\cons((a,b),\zip(x,z))) \\
 & = & \cons(\pair(f,g)(a,b),\map(\pair(f,g))(\zip(x,z))) \\
 & = & \cons(\pair(f,g)(a,b),\zip(\map(f)(x),\map(g)(z))) \\
 & = & \cons((f(a),g(b)),\zip(\map(f)(x),\map(g)(z))) \\
 & = & \zip(\cons(f(a),\map(f)(x)),\cons(g(b),\map(g)(z))) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(\cons(b,z))) \\
 & = & \zip(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

The length of a zipped list:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, with $x \in \lists{A}$ and $y \in \lists{B}$. Then $$\length(\zip(x,y)) = \nmin(\length(x),\length(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,y)) \\
 & = & \length(\zip(x,\nil)) \\
 & = & \length(\nil) \\
 & = & \zero \\
 & = & \nmin(\length(x),\zero) \\
 & = & \nmin(\length(x),\length(\nil)) \\
 & = & \nmin(\length(x),\length(y)) \\
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $y$ and let $b \in B$. We consider two cases: either $x = \nil$ or $x = \cons(a,z)$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,\cons(b,y))) \\
 & = & \length(\zip(\nil,\cons(b,y))) \\
 & = & \length(\nil) \\
 & = & \zero \\
 & = & \nmin(\zero,\length(\cons(b,y))) \\
 & = & \nmin(\length(\nil),\length(\cons(b,y))) \\
 & = & \nmin(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose $x = \cons(b,z)$; now we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,\cons(b,y))) \\
 & = & \length(\zip(\cons(a,z),\cons(b,y))) \\
 & = & \length(\cons((a,b),\zip(z,y))) \\
 & = & \next(\length(\zip(z,y))) \\
 & = & \next(\min(\length(z),\length(y))) \\
 & = & \nmin(\next(\length(z)),\next(\length(y))) \\
 & = & \nmin(\length(\cons(a,z)),\length(\cons(b,y))) \\
 & = & \nmin(x),\length(\cons(b,y))) \\
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\zip$ is kind of associative:

<div class="result">
<div class="thm"><p>
Let $A$, $B$, and $C$ be sets, with $x \in \lists{A}$, $y \in \lists{B}$, and $z \in \lists{C}$. Then the following hold.

1. $\zip(\zip(x,y),z) = \map(\assocL)(\zip(x,\zip(y,z)))$.
2. $\zip(x,\zip(y,z)) = \map(\assocR)(\zip(\zip(x,y),z))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \zip(\zip(x,y),z) \\
 & = & \zip(\zip(\nil,y),z) \\
 & = & \zip(\nil,z) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zip(\nil,\zip(y,z)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 & = & \zip(\zip(\cons(a,x),\nil),z) \\
 & = & \zip(\nil,z) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\nil)) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\zip(\nil,z))) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed. Similarly, if $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 & = & \zip(\zip(\cons(a,x),y),\nil) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\nil)) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,u)$ and $z = \cons(c,v)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 & = & \zip(\zip(\cons(a,x),\cons(b,u)),\cons(c,v)) \\
 & = & \zip(\cons((a,b),\zip(x,u)),\cons(c,v)) \\
 & = & \cons(((a,b),c),\zip(\zip(x,u),v)) \\
 & = & \cons(\assocL(a,(b,c)),\map(\assocL)(\zip(x,\zip(u,v)))) \\
 & = & \map(\assocL)(\cons((a,(b,c)),\zip(x,\zip(u,v)))) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\cons((b,c),\zip(u,v)))) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\zip(\cons(b,u),\cons(c,v)))) \\
 & = & \map(\assocL)(\zip(\cons(a,x),\zip(y,z))) \\
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \zip(x,\zip(y,z)) \\
 & = & \id(\zip(x,\zip(y,z))) \\
 & = & \map(\id)(\zip(x,\zip(y,z))) \\
 & = & \map(\assocR \circ \assocL)(\zip(x,\zip(y,z))) \\
 & = & \map(\assocR)(\map(\assocL)(\zip(x,\zip(y,z)))) \\
 & = & \map(\assocR)(\zip(\zip(x,y),z)) 
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

How about $\zipPad$? We want a signature like $$A \times B \rightarrow \lists{A} \times \lists{B} \rightarrow \lists{A \times B},$$ from a function $$\foldr{\delta}{\psi} : \lists{A} \rightarrow \lists{A \times B}^{\lists{B}}.$$ Let $\alpha \in A$ and $\beta \in B$ be the "pad" elements. Now $\delta : \lists{A \times B}^{\lists{B}}$ should satisfy
$$\begin{eqnarray*}
 &   & \map((\alpha,-))(y) \\
 & = & \zipPad(\alpha,\beta)(\nil,y) \\
 & = & \foldr{\delta}{\psi}(\nil)(y) \\
 & = & \delta(y),
\end{eqnarray*}$$
and $\psi : \lists{A} \times \lists{A \times B}^{\lists{B}} \rightarrow \lists{A \times B}^{\lists{B}}$ should satisfy
$$\begin{eqnarray*}
 &   & \cons((a,\beta),\foldr{\delta}{\psi}(x)(\nil)) \\
 & = & \cons((a,\beta),\zipPad(\alpha,\beta)(x,\nil)) \\
 & = & \zipPad(\alpha,\beta)(\cons(a,x),\nil) \\
 & = & \foldr{\delta}{\psi}(\cons(a,x))(\nil) \\
 & = & \psi(a,\foldr{\delta}{\psi}(x))(\nil)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \cons((a,b),\zipPad(x,y)) \\
 & = & \zipPad(\alpha,\beta)(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\delta}{\psi}(\cons(a,x))(\cons(b,y)) \\
 & = & \psi(a,\foldr{\delta}{\psi}(x))(\cons(b,y)).
\end{eqnarray*}$$
With this in mind, we define $\zipPad$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. Define $\delta : A \rightarrow \lists{A \times B}^{\lists{B}}$ by $$\delta(u)(y) = \map((u,-))(y)$$ and define $\psi : B \rightarrow \lists{A} \times \lists{A \times B}^{\lists{B}} \rightarrow \lists{A\times B}^{\lists{B}}$ by $$\psi(v)(x,f)(z) = \left\{\begin{array}{ll} \cons((x,v),f(z)) & \mathrm{if}\ z = \nil \\ \cons((x,y),f(w)) & \mathrm{if}\ z = \cons(y,w). \end{array}\right.$$ We then define $\zipPad : A \times B \rightarrow \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$ by $$\zipPad(u,v)(x,y) = \foldr{\delta(u)}{\psi(v)}(x)(y).$$
</p></div>
</div>

The implementation from the definition does the job:

```haskell

> zipPad' :: (ListOf t) => a -> b -> t a -> t b -> t (a,b)
> zipPad' u v = foldr (delta u) (psi v)
>   where
>     psi :: (ListOf t) => b -> a -> (t b -> t (a,b)) -> t b -> t (a,b)
>     psi v x f z = case listShape z of
>       Nil       -> cons (x,v) (f nil)
>       Cons y ys -> cons (x,y) (f ys)
>
>     delta :: (ListOf t) => a -> t b -> t (a,b)
>     delta u z = map (\t -> (u,t)) z

```

But again, a more straightforward implementation is possible.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. The following hold for all $\alpha, a \in A$, $x \in \lists{A}$, $\beta, b \in B$, and $y \in \lists{B}$.

1. $\zipPad(\alpha,\beta)(\nil,y) = \map((\alpha,-))(y)$.
2. $\zipPad(\alpha,\beta)(x,\nil) = \map((-,\beta))(x)$.
3. $\zipPad(\alpha,\beta)(\cons(a,x),\cons(b,y)) = \cons((a,b),\zipPad(\alpha,\beta)(x,y))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \zipPad(\alpha,\beta)(\nil,y) \\
 & = & \foldr{\delta(\alpha)}{\psi(\beta)}(\nil)(y) \\
 & = & \delta(\alpha)(y) \\
 & = & \map((\alpha,-))(y)
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad(\alpha,\beta)(\nil,\nil) \\
 & = & \nil \\
 & = & \map((-,\beta))(\nil) \\
 & = & \map((-,\beta))(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \zipPad(\alpha,\beta)(\cons(a,x),\nil) \\
 & = & \foldr{\delta(\alpha)}{\psi(\beta)}(\cons(a,x))(\nil) \\
 & = & \psi(\beta)(a,\foldr{\delta(\alpha)}{\psi(\beta)}(x))(\nil) \\
 & = & \cons((a,\beta),\foldr{\delta(\alpha)}{\psi(\beta)}(x)(\nil)) \\
 & = & \cons((a,\beta),\zipPad(\alpha,\beta)(x,\nil)) \\
 & = & \cons((a,\beta),\map((-,\beta))(x)) \\
 & = & \map((-,\beta))(\cons(a,x))
\end{eqnarray*}$$
as needed.
3. We have
$$\begin{eqnarray*}
 &   & \zipPad(\alpha,\beta)(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\delta(\alpha)}{\psi(\beta)}(\cons(a,x))(\cons(b,y)) \\
 & = & \psi(\beta)(a,\foldr{\delta(\alpha)}{\psi(\beta)}(x))(\cons(b,y)) \\
 & = & \cons((a,b),\foldr{\delta(\alpha)}{\psi(\beta)}(x)(y)) \\
 & = & \cons((a,b),\zipPad(\alpha,\beta)(x,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> zipPad :: (ListOf t) => a -> b -> t a -> t b -> t (a,b)
> zipPad u v x y = case listShape x of
>   Nil       -> map (\w -> (u,w)) y
>   Cons a as -> case listShape y of
>     Nil       -> map (\w -> (w,v)) x
>     Cons b bs -> cons (a,b) (zipPad u v as bs)

Now $\zipPad$ satisfies several properties analogous to those of $\zip$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then for all $\alpha \in A$, $\beta \in B$, $x \in \lists{A}$, and $y \in \lists{B}$ we have $$\map(\swap)(\zipPad(\alpha,\beta)(x,y)) = \zipPad(\beta,\alpha)(y,x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zipPad(\alpha,\beta)(x,y)) \\
 & = & \map(\swap)(\zipPad(\alpha,\beta)(\nil,y)) \\
 & = & \map(\swap)(\map((\alpha,-))(y)) \\
 & = & (\map(\swap) \circ \map((\alpha,-)))(y) \\
 & = & \map(\swap \circ (\alpha,-))(y) \\
 & = & \map((-,\alpha))(y) \\
 & = & \zipPad(\beta,\alpha)(y,\nil) \\
 & = & \zipPad(\beta,\alpha)(y,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we consider two cases for $y$; either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zipPad(\alpha,\beta)(\cons(a,x),y)) \\
 & = & \map(\swap)(\zipPad(\alpha,\beta)(\cons(a,x),\nil)) \\
 & = & \map(\swap)(\map((-,\beta))(\cons(a,x))) \\
 & = & (\map(\swap) \circ \map((-,\beta)))(\cons(a,x)) \\
 & = & \map(\swap \circ (-,\beta))(\cons(a,x)) \\
 & = & \map((\beta,-))(\cons(a,x)) \\
 & = & \zipPad(\alpha,\beta)(\nil,\cons(a,x)) \\
 & = & \zipPad(\alpha,\beta)(y,\cons(a,x))
\end{eqnarray*}$$
as needed. Finally, suppose $y = \cons(b,w)$. Then we have
$$\begin{eqnarray*}
 &   & \map(\swap)(\zipPad(\alpha,\beta)(\cons(a,x),y)) \\
 & = & \map(\swap)(\zipPad(\alpha,\beta)(\cons(a,x),\cons(b,w))) \\
 & = & \map(\swap)(\cons((a,b),\zipPad(\alpha,\beta)(x,w)) \\
 & = & \cons(\swap((a,b)),\map(\swap)(\zipPad(\alpha,\beta)(x,w))) \\
 & = & \cons((b,a),\zipPad(\beta,\alpha)(w,x)) \\
 & = & \zipPad(\beta,\alpha)(\cons(b,w),\cons(a,x)) \\
 & = & \zipPad(\beta,\alpha)(y,\cons(a,x)) \\
\end{eqnarray*}$$
as needed.
</p></div>
</div>

and...

<div class="result">
<div class="thm"><p>
Let $A$, $B$, $U$, and $V$ be sets, with functions $f : A \rightarrow U$ and $g : B \rightarrow V$. Then for all $\alpha \in A$, $\beta \in B$, $x \in \lists{A}$, and $y \in \lists{B}$, we have $$\map(\pair(f,g))(\zipPad(\alpha,\beta)(x,y)) = \zipPad(f(\alpha),g(\beta))(\map(f)(x),\map(g)(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zipPad(\alpha,\beta)(x,y)) \\
 & = & \map(\pair(f,g))(\zipPad(\alpha,\beta)(\nil,y)) \\
 & = & \map(\pair(f,g))(\map((\alpha,-))(y)) \\
 & = & (\map(\pair(f,g)) \circ \map((\alpha,-)))(y) \\
 & = & \map(\pair(f,g) \circ (\alpha,-))(y) \\
 & = & \map((f(\alpha),g(-)))(y) \\
 & = & \map((f(\alpha),-) \circ g)(y) \\
 & = & \map((f(\alpha),-))(\map(g)(y)) \\
 & = & \zipPad(f(\alpha),g(\beta))(\nil,\map(g)(y)) \\
 & = & \zipPad(f(\alpha),g(\beta))(x,\map(g)(y))
\end{eqnarray*}$$
as needed. Now suppose the equality holds for some $x$ and let $a \in A$. We consider two cases for $y$; either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zipPad(\alpha,\beta)(\cons(a,x),y)) \\
 & = & \map(\pair(f,g))(\zipPad(\alpha,\beta)(\cons(a,x),\nil)) \\
 & = & \map(\pair(f,g))(\map((-,\beta))(\cons(a,x))) \\
 & = & (\map(\pair(f,g)) \circ \map((-,\beta)))(\cons(a,x)) \\
 & = & \map(\pair(f,g) \circ (-,\beta))(\cons(a,x)) \\
 & = & \map((f(-),g(\beta)))(\cons(a,x)) \\
 & = & \map((-,g(\beta)) \circ f)(\cons(a,x)) \\
 & = & \map((-,g(\beta)))(\map(f)(\cons(a,x))) \\
 & = & \zipPad(f(\alpha),g(\beta))(\map(f)(\cons(a,x)),\nil) \\
 & = & \zipPad(f(\alpha),g(\beta))(\map(f)(\cons(a,x)),y) \\
\end{eqnarray*}$$
as needed. If $y = \cons(b,w)$, we have
$$\begin{eqnarray*}
 &   & \map(\pair(f,g))(\zipPad(\alpha,\beta)(\cons(a,x),\cons(b,w))) \\
 & = & \map(\pair(f,g))(\cons((a,b),\zipPad(\alpha,\beta)(x,w))) \\
 & = & \cons(\pair(f,g)(a,b),\map(\pair(f,g))(\zipPad(\alpha,\beta)(x,w))) \\
 & = & \cons((f(a),g(b)),\zipPad(f(\alpha),g(\beta))(\map(f)(x),\map(g)(w))) \\
 & = & \zipPad(f(\alpha),g(\beta))(\cons(f(a),\map(f)(x)),\cons(g(b),\map(g)(w))) \\
 & = & \zipPad(f(\alpha),g(\beta))(\map(f)(\cons(a,x)),\map(g)(\cons(b,w))) \\
 & = & \zipPad(f(\alpha),g(\beta))(\map(f)(\cons(a,x)),\map(g)(y)) \\
\end{eqnarray*}$$
as needed.
</p></div>
</div>

and...

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, with $\alpha \in A$, $\beta \in B$, $x \in \lists{A}$, and $y \in \lists{B}$. Then $$\length(\zipPad(\alpha,\beta)(x,y)) = \nmax(\length(x),\length(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zipPad(\alpha,\beta)(x,y)) \\
 & = & \length(\zipPad(\alpha,\beta)(\nil,y)) \\
 & = & \length(\map((\alpha,-))(y)) \\
 & = & \length(y) \\
 & = & \nmax(\zero,\length(y)) \\
 & = & \nmax(\length(\nil),\length(y)) \\
 & = & \nmax(\length(x),\length(y)) \\
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. We consider two possibilities for $y$: either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zipPad(\alpha,\beta)(\cons(a,x),y)) \\
 & = & \length(\zipPad(\alpha,\beta)(\cons(a,x),\nil)) \\
 & = & \length(\map((-,\beta))(\cons(a,x))) \\
 & = & \length(\cons(a,x)) \\
 & = & \nmax(\length(\cons(a,x)),\zero) \\
 & = & \nmax(\length(\cons(a,x)),\length(\nil)) \\
 & = & \nmax(\length(\cons(a,x)),\length(y)) \\
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,w)$. Now
$$\begin{eqnarray*}
 &   & \length(\zipPad(\alpha,\beta)(\cons(a,x),y)) \\
 & = & \length(\zipPad(\alpha,\beta)(\cons(a,x),\cons(b,w))) \\
 & = & \length(\cons((a,b),\zipPad(\alpha,\beta)(x,w))) \\
 & = & \next(\length(\zipPad(\alpha,\beta)(x,w))) \\
 & = & \next(\nmax(\length(x),\length(w))) \\
 & = & \nmax(\next(\length(x)),\next(\length(w))) \\
 & = & \nmax(\length(\cons(a,x)),\length(\cons(b,w))) \\
 & = & \nmax(\length(\cons(a,x)),\length(y)) \\
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\zipPad$ is also kind of associative:

<div class="result">
<div class="thm"><p>
Let $A$, $B$, and $C$ be sets, with $\alpha \in A$, $\beta \in B$, $\gamma \in C$, $x \in \lists{A}$, $y \in \lists{B}$, and $z \in \lists{C}$. Then the following hold.

1. $$\begin{eqnarray*}
 &   & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(x,y),z) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z))).
\end{eqnarray*}$$
2. $$\begin{eqnarray*}
 &   & \zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z)) \\
 & = & \map(\assocR)(\zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(x,y),z)).
\end{eqnarray*}$$
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(x,y),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\nil,y),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\nil,z) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\nil,\zipPad(\beta,\gamma)(y,z))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),y),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),\nil),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\nil,z) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\nil)) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zipPad(\beta,\gamma)(\nil,z))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zipPad(\beta,\gamma)(y,z)))
\end{eqnarray*}$$
as claimed. Similarly, if $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),y),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),y),\nil) \\
 & = & \nil \\
 & = & \map(\assocL)(\nil) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\nil)) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zipPad(\beta,\gamma)(y,\nil))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zipPad(\beta,\gamma)(y,z))) \\
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,u)$ and $z = \cons(c,v)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),y),z) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(\cons(a,x),\cons(b,u)),\cons(c,v)) \\
 & = & \zipPad((\alpha,\beta),\gamma)(\cons((a,b),\zipPad(\alpha,\beta)(x,u)),\cons(c,v)) \\
 & = & \cons(((a,b),c),\zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(x,u),v)) \\
 & = & \cons(\assocL(a,(b,c)),\map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(u,v)))) \\
 & = & \map(\assocL)(\cons((a,(b,c)),\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(u,v)))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\cons((b,c),\zipPad(\beta,\gamma)(u,v)))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zipPad(\beta,\gamma)(\cons(b,u),\cons(c,v)))) \\
 & = & \map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(\cons(a,x),\zip(y,z))) \\
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z)) \\
 & = & \id(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z))) \\
 & = & \map(\id)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z))) \\
 & = & \map(\assocR \circ \assocL)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z))) \\
 & = & \map(\assocR)(\map(\assocL)(\zipPad(\alpha,(\beta,\gamma))(x,\zipPad(\beta,\gamma)(y,z)))) \\
 & = & \map(\assocR)(\zipPad((\alpha,\beta),\gamma)(\zipPad(\alpha,\beta)(x,y),z))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\zip$ and $\zipPad$.

> -- map(swap)(zip(x,y)) == zip(y,x)
> _test_zip_swap :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_zip_swap _ x y =
>   (map swap (zip x y)) `listEq` (zip y x)
> 
> 
> -- length(zip(x,y)) == min(length(x),length(y))
> _test_zip_length :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_zip_length _ x y =
>   (length (zip x y)) == (min (length x) (length y))
> 
> 
> -- zip(zip(x,y),z) == map(assocL)zip(x,zip(y,z))
> _test_zip_zip_left :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_zip_zip_left _ x y z =
>   (zip (zip x y) z) `listEq` map assocL (zip x (zip y z))
> 
> 
> -- zip(zip(x,y),z) == map(assocR)zip(x,zip(y,z))
> _test_zip_zip_right :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_zip_zip_right _ x y z =
>   (zip x (zip y z)) `listEq` map assocR (zip (zip x y) z)
> 
> 
> -- zip'(x,y) == zip(x,y)
> _test_zip_alt :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_zip_alt _ x y =
>   (zip' x y) `listEq` (zip x y)
> 
> 
> -- map(swap)(zipPad(u,v)(x,y)) == zipPad(v,u)(y,x)
> _test_zipPad_swap :: (ListOf t, Eq a)
>   => t a -> a -> a -> t a -> t a -> Bool
> _test_zipPad_swap _ u v x y =
>   (map swap (zipPad u v x y)) `listEq` (zipPad v u y x)
> 
> 
> -- length(zipPad(u,v)(x,y)) == max(length(x),length(y))
> _test_zipPad_length :: (ListOf t, Eq a)
>   => t a -> a -> a -> t a -> t a -> Bool
> _test_zipPad_length _ u v x y =
>   (length (zipPad u v x y)) == (max (length x) (length y))
> 
> 
> -- zipPad((a,b),c)(zipPad(a,b)(x,y),z)
> --   == map(assocL)zipPad(a,(b,c))(x,zipPad(b,c)(y,z))
> _test_zipPad_zipPad_left :: (ListOf t, Eq a)
>   => t a -> a -> a -> a -> t a -> t a -> t a -> Bool
> _test_zipPad_zipPad_left _ a b c x y z =
>   listEq
>     (zipPad (a,b) c (zipPad a b x y) z)
>     (map assocL (zipPad a (b,c) x (zipPad b c y z)))
> 
> 
> -- zipPad((a,b),c)(zipPad(a,b)(x,y),z)
> --   == map(assocR)zipPad(a,(b,c))(x,zipPad(b,c)(y,z))
> _test_zipPad_zipPad_right :: (ListOf t, Eq a)
>   => t a -> a -> a -> a -> t a -> t a -> t a -> Bool
> _test_zipPad_zipPad_right _ a b c x y z =
>   listEq
>     (zipPad a (b,c) x (zipPad b c y z))
>     (map assocR (zipPad (a,b) c (zipPad a b x y) z))
> 
> 
> -- zipPad'(x,y) == zipPad(x,y)
> _test_zipPad_alt :: (ListOf t, Eq a)
>   => t a -> a -> a -> t a -> t a -> Bool
> _test_zipPad_alt _ u v x y =
>   (zipPad' u v x y) `listEq` (zipPad u v x y)

And the suite:

> -- run all tests for zip
> _test_zip :: (ListOf t, Arbitrary (t n), Show (t n), Natural n, Arbitrary n, Show n)
>   => t n -> n -> Int -> Int -> IO ()
> _test_zip t n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_zip_swap t)
>   , quickCheckWith args (_test_zip_length t)
>   , quickCheckWith args (_test_zip_zip_left t)
>   , quickCheckWith args (_test_zip_zip_right t)
>   , quickCheckWith args (_test_zip_alt t)
> 
>   , quickCheckWith args (_test_zipPad_swap t)
>   , quickCheckWith args (_test_zipPad_length t)
>   , quickCheckWith args (_test_zipPad_zipPad_left t)
>   , quickCheckWith args (_test_zipPad_zipPad_right t)
>   , quickCheckWith args (_test_zipPad_alt t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_zip :: IO ()
> main_zip = _test_zip (nil :: List Nat) (zero :: Nat) 20 100
