---
title: At
author: nbloomf
date: 2017-04-28
tags: arithmetic-made-difficult, literate-haskell
---

> module At
>   ( at, _test_at, main_at
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import Minus
> import LessThanOrEqualTo
>
> import Lists
> import Reverse
> import Cat
> import Length
> 
> import Prelude ()
> import Test.QuickCheck

In this post we'll investigate $\at$, which extracts the element at an arbitrary position in a list. First, we need $\head$, which extracts the *first* element of a list. To a first approximation $\head$ has a signature like $$\lists{A} \rightarrow A,$$ and certainly we want $\head(\cons(a,x)) = a$. But what about $\head(\nil)$? In this case there is no element to extract. Taking a cue from our definition of $\nminus$, we will make $\head$ return not an $A$, but a $\ast + A$, letting the $\ast$ represent $\head(\nil)$. Now $\head$ can be expressed as a $\foldr{\ast}{\ast}$ as follows.

<div class="result">
<div class="defn"><p>
Define $\varphi : A \times (\ast + A) \rightarrow \ast + A$ by $$\varphi(a,b) = a.$$ Now we define $\head : \lists{A} \rightarrow \ast + A$ by $$\head = \foldr{\ast}{\varphi}.$$

In Haskell:

> head :: (List t) => t a -> Maybe a
> head = foldr Nothing phi
>   where
>     phi a _ = Just a

</p></div>
</div>

Tracing $\head$ we can see that it indeed extracts the first element of a list.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $a \in A$ and $x \in \lists{A}$, we have $$\head(\cons(a,x)) = a.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \head(\cons(a,x)) \\
 & = & \foldr{\ast}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\ast}{\varphi}(x)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

There's a catch here: $\head$ should in principle do a constant amount of work. It needs to deconstruct only the outermost constructor of its argument. But if we're implementing $\foldr{\ast}{\ast}$ using a language which eagerly evaluates function arguments, it will happily march down the list all the way to the end. Haskell is lazy, so this won't be a problem for us, but it's worth mentioning. Maybe we need a new recursion operator!

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $a \in A$ and $x \in \lists{A}$ with $x \neq \nil$, we have $$\head(\snoc(a,x)) = \head(x).$$
</p></div>

<div class="proof"><p>
If $x \neq \nil$, we have $x = \cons(b,y)$ for some $b \in A$ and $y \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \head(\snoc(a,x)) \\
 & = & \head(\snoc(a,\cons(b,y))) \\
 & = & \head(\cons(b,\snoc(a,y))) \\
 & = & b \\
 & = & \head(\cons(b,y)) \\
 & = & \head(x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

With $\head$ in hand, we can extract arbitrary elements from a list as follows.

<div class="result">
<div class="defn"><p>
Define $\varphi : \lists{A} \rightarrow \ast + A$ by $$\varphi(a) = \ast,$$ $\beta : \nats \times \lists{A} \rightarrow \bool$ by $$\beta(k,x) = \iszero(k) \bor \isnil(x),$$ $\psi : \nats \times \lists{A} \rightarrow \ast + A$ by $$\psi(k,x) = \head(x),$$ and $\omega : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\omega(k,x) = \tail(x).$$ We then define $\at : \lists{A} \times \nats \rightarrow \ast + A$ by $$\at(x,k) = \bailrec{\varphi}{\beta}{\psi}{\omega}(k,x).$$

In Haskell:

> at :: (Natural n, List t) => t a -> n -> Maybe a
> at x k = bailoutRec phi beta psi omega k x
>   where
>     phi   _   = Nothing
>     beta  k x = or (isZero k) (isNil x)
>     psi   _ x = head x
>     omega _ x = tail x

</p></div>
</div>

For the remainder of this post, we let $\Theta$ denote $\bailrec{\varphi}{\beta}{\psi}{\omega}$ as in this definition. First lets trace some special cases.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $a,b \in A$, $x \in \lists{A}$, and $k \in \nats$.

1. $\at(\nil,k) = \ast$.
2. $\at(\cons(a,x),\next(\zero)) = a$.
3. $\at(\cons(a,\cons(b,x)),\next(\next(\zero))) = b$.
</p></div>

<div class="proof"><p>
1. We consider two cases: $k = \zero$ and $k \neq \zero$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\zero) \\
 & = & \Theta(\zero,\nil) \\
 & = & \varphi(\nil) \\
 & = & \ast
\end{eqnarray*}$$
as claimed. If $k = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\next(m)) \\
 & = & \Theta(\next(m),\nil) \\
 & = & \psi(m,\nil) \\
 & = & \head(\nil) \\
 & = & \ast
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\next(\zero)) \\
 & = & \Theta(\next(\zero),\cons(a,x)) \\
 & = & \psi(\zero,\cons(a,x)) \\
 & = & \head(\cons(a,x)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \at(\cons(a,\cons(b,x)),\next(\next(\zero))) \\
 & = & \Theta(\next(\next(\zero)),\cons(a,\cons(b,x))) \\
 & = & \Theta(\next(\zero),\omega(\next(\zero),\cons(a,\cons(b,x)))) \\
 & = & \Theta(\next(\zero),\tail(\cons(a,\cons(b,x)))) \\
 & = & \Theta(\next(\zero),\cons(b,x)) \\
 & = & \at(\cons(b,x),\next(\zero)) \\
 & = & b
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

More generally:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have $$\at(\cons(a,x),\next(\next(k))) = \at(x,\next(k)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \at(\cons(a,x),\next(\next(k))) \\
 & = & \Theta(\next(\next(k)),\cons(a,x)) \\
 & = & \Theta(\next(k),\omega(\next(k),\cons(a,x))) \\
 & = & \Theta(\next(k),\tail(\cons(a,x))) \\
 & = & \Theta(\next(k),x) \\
 & = & \at(x,\next(k))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We also have:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and let $z \in \lists{A}$. Then $$\at(z,\length(z)) = \head(\rev(z)).$$
</p></div>

<div class="proof"><p>
We consider two cases: either $z = \nil$ or $z = \cons(a,x)$ for some $a \in A$ and $x \in \lists{A}$. If $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \at(\nil,\length(\nil)) \\
 & = & \at(\nil,\zero) \\
 & = & \ast \\
 & = & \head(\nil)
\end{eqnarray*}$$
as claimed.

Suppose instead that $z = \cons(a,x)$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \at(z,\length(z)) \\
 & = & \at(\cons(a,\nil),\length(\cons(a,\nil))) \\
 & = & \at(\cons(a,\nil),\next(\zero)) \\
 & = & a \\
 & = & \head(\cons(a,\nil)) \\
 & = & \head(\rev(\cons(a,\nil))) \\
 & = & \head(\rev(z))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $b \in A$. Now we have
$$\begin{eqnarray*}
 &   & \at(z,\length(z)) \\
 & = & \at(\cons(a,\cons(b,x)),\length(\cons(a,\cons(b,x)))) \\
 & = & \at(\cons(a,\cons(b,x)),\next(\next(\length(x)))) \\
 & = & \at(\cons(b,x),\next(\length(x))) \\
 & = & \at(\cons(b,x),\length(\cons(b,x))) \\
 & = & \head(\rev(\cons(b,x))) \\
 & = & \head(\snoc(a,\rev(\cons(b,x)))) \\
 & = & \head(\rev(\cons(a,\cons(b,x)))) \\
 & = & \head(\rev(z))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

We can characterize the $k$ such that $\at(x,k) = \ast$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$ we have the following.

1. If $\nleq(\next(\length(x)),k)$, then $\at(x,k) = \ast$.
2. If $\nleq(\next(\zero),k)$ and $\nleq(k,\length(x))$ then $\at(x,k) \neq \ast$.
</p></div>

<div class="proof"><p>
1. We proceed by induction on $k$. For the base case $k = \zero$, note that $\nleq(\next(\length(x)),\zero)$ is false, so the implication holds vacuously. For the inductive step, suppose the implication holds for all $x \in \lists{A}$ for some $k$. Suppose further that $x \in \lists{A}$ such that $\nleq(\next(\length(x)),\next(k))$. We consider two cases for $x$: either $x = \nil$ or $x = \cons(a,y)$ for some $y$. If $x = \nil$ we have $\at(\nil,\next(k)) = \ast$ as claimed. If $x = \cons(a,y)$, we have
$$\begin{eqnarray*}
 &   & \nleq(\next(\length(x)),\next(k)) \\
 & = & \nleq(\length(x),k) \\
 & = & \nleq(\length(\cons(a,y),k) \\
 & = & \nleq(\next(\length(y)),k).
\end{eqnarray*}$$
Note in particular that $k = \next(m)$ for some $m$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(k)) \\
 & = & \at(\cons(a,y),\next(\next(m))) \\
 & = & \at(y,\next(m)) \\
 & = & \at(y,k) \\
 & = & \ast
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $k$. For the base case $k = \zero$, note that $\nleq(\next(\zero),k) = \bfalse$, so the implication holds vacuously. For the inductive step, suppose the implication holds for all $x \in \lists{A}$ for some $k \in \nats$. Let $x \in \lists{A}$, and suppose further that $\nleq(\next(\zero),\next(k))$ and $\nleq(\next(k),\length(x))$. Note that $x \neq \nil$; say $x = \cons(a,y)$. We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(k)) \\
 & = & \at(\cons(a,y),\next(\zero)) \\
 & = & a \\
 & \neq & \ast
\end{eqnarray*}$$
as needed. If $k \neq \zero$, we have $k = \next(m)$ for some $m \in \nats$. Note that $\nleq(\next(\zero),k)$ and $\nleq(k,\length(y))$. Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(k)) \\
 & = & \at(\cons(a,y),\next(\next(m))) \\
 & = & \at(y,\next(m)) \\
 & = & \at(y,k) \\
 & \neq & \ast
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\at$ interacts with $\snoc$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Let $a \in A$, $x \in \lists{A}$, and $k \in \nats$. Now if $\nleq(k,\length(x))$, we have $$\at(\snoc(a,x),k) = \at(x,k).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, if $\nleq(k,\length(\nil))$ we have $k = \zero$. So
$$\begin{eqnarray*}
 &   & \at(\snoc(a,x),k) \\
 & = & \at(\snoc(a,x),\zero) \\
 & = & \ast \\
 & = & \at(x,\zero) \\
 & = & \at(x,k)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the implication holds for all $a \in A$ and $k \in \nats$ for some $x \in \lists{A}$, and let $b \in A$. Suppose further that $\nleq(k,\length(\cons(b,x))$. We consider three possibilities for $k$: either $k = \zero$, $k = \next(\zero)$, or $k = \next(\next(m))$ for some $m$.

If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),k) \\
 & = & \at(\snoc(a,\cons(b,x)),\zero) \\
 & = & \ast \\
 & = & \at(\cons(b,x),\zero) \\
 & = & \at(\cons(b,x),k)
\end{eqnarray*}$$
as claimed.

If $k = \next(\zero)$, we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),k) \\
 & = & \at(\snoc(a,\cons(b,x)),\next(\zero)) \\
 & = & \at(\cons(b,\snoc(a,x)),\next(\zero)) \\
 & = & b \\
 & = & \at(\cons(b,x),\next(\zero)) \\
 & = & \at(\cons(b,x),k)
\end{eqnarray*}$$
as claimed.

Finally, suppose $k = \next(\next(m))$. Now
$$\begin{eqnarray*}
 &   & \nleq(k,\length(\cons(b,x))) \\
 & = & \nleq(\next(\next(m)),\next(\length(x)) \\
 & = & \nleq(\next(m),\length(x)).
\end{eqnarray*}$$
Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(\snoc(a,\cons(b,x)),k) \\
 & = & \at(\snoc(a,\cons(b,x)),\next(\next(m))) \\
 & = & \at(\cons(b,\snoc(a,x)),\next(\next(m))) \\
 & = & \at(\snoc(a,x),\next(m)) \\
 & = & \at(x,\next(m)) \\
 & = & \at(\cons(b,x),\next(\next(m))) \\
 & = & \at(\cons(b,x),k)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\at$ interacts with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ and $k \in \nats$, we have $$\at(\cat(x,y),k) = \left\{ \begin{array}{ll} \at(x,k) & \mathrm{if}\ \nleq(k,\length(x)) \\ \at(y,\nminus(k,\length(x))) & \mathrm{if}\ \nleq(\next(\length(x)),k). \end{array} \right.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, note that $\cat(x,y) = x$. Now if $\nleq(k,\length(x))$, we have
$$\begin{eqnarray*}
 &   & \at(\cat(x,y),k) \\
 & = & \at(x,k)
\end{eqnarray*}$$
as claimed.
If $\nleq(\next(\length(x)),k)$, we have
$$\begin{eqnarray*}
 &   & \at(\cat(x,y),k) \\
 & = & \at(x,k) \\
 & = & \ast \\
 & = & \at(\nil,\nminus(k,\length(x)))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $x \in \lists{A}$ and $k \in \nats$ for some $y \in \lists{A}$, and let $a \in A$. First suppose $\nleq(k,\length(x))$. Now
$$\begin{eqnarray*}
 &   & \nleq(k,\length(x)) \\
 & = & \nleq(k,\next(\length(x))) \\
 & = & \nleq(k,\length(\snoc(a,x))).
\end{eqnarray*}$$
So by the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \at(\cat(x,\cons(a,y)),k) \\
 & = & \at(\cat(\snoc(a,x),y),k) \\
 & = & \at(\snoc(a,x),k) \\
 & = & \at(x,k)
\end{eqnarray*}$$
as needed.
Next suppose $\nleq(\next(\length(x)),k)$. We consider two possibilities: either $k = \next(\length(x))$ or $\nleq(\next(\next(\length(x)),k)$.

First suppose $k = \next(\length(x))$. Note that $$\next(\length(x)) = \length(\snoc(a,x)),$$ so using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \at(\cat(x,\cons(a,y)),k) \\
 & = & \at(\cat(\snoc(a,x),y),k) \\
 & = & \at(\snoc(a,x),k) \\
 & = & \at(\snoc(a,x),\length(\snoc(a,x))) \\
 & = & \head(\rev(\snoc(a,x))) \\
 & = & \head(\cons(a,\rev(x))) \\
 & = & a \\
 & = & \at(\cons(a,y),\next(\zero)) \\
 & = & \at(\cons(a,y),\nminus(\next(\length(x)),\length(x))) \\
 & = & \at(\cons(a,y),\nminus(k,\length(x)))
\end{eqnarray*}$$
as needed.

Next suppose $\nleq(\next(\next(\length(x))),k)$. Say $k = \next(\next(m))$. Again using the inductive hypothesis, and noting that $\length(\snoc(a,x)) = \next(\length(x))$, we now have
$$\begin{eqnarray*}
 &   & \at(\cat(x,\cons(a,y)),k) \\
 & = & \at(\cat(\snoc(a,x),y),k) \\
 & = & \at(y,\nminus(k,\length(\snoc(a,x))) \\
 & = & \at(y,\nminus(k,\next(\length(x)))) \\
 & = & \at(y,\nminus(\next(\next(m)),\next(\length(x)))) \\
 & = & \at(y,\next(\nminus(\next(m),\next(\length(x))))) \\
 & = & \at(\cons(a,y),\next(\next(\nminus(\next(m),\next(\length(x)))))) \\
 & = & \at(\cons(a,y),\next(\next(\nminus(m,\length(x))))) \\
 & = & \at(\cons(a,y),\nminus(\next(\next(m)),\length(x))) \\
 & = & \at(\cons(a,y),\nminus(k,\length(x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\at$ interacts with $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Let $x \in \lists{A}$ and $u,v \in \nats$. If $\nplus(u,v) = \next(\length(x))$, then we have $$\at(x,u) = \at(\rev(u),v).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $u$. For the base case $u = \zero$, note that if $\nplus(u,v) = \next(\length(x))$ we have $v = \next(\length(x))$. Note also that $\length(x) = \length(\rev(x))$. So in this case we have
$$\begin{eqnarray*}
 &   & \at(x,u) \\
 & = & \at(x,\zero) \\
 & = & \ast \\
 & = & \at(\rev(x),\next(\length(\rev(x)))) \\
 & = & \at(\rev(x),\next(\length(x))) \\
 & = & \at(\rev(x),v)
\end{eqnarray*}$$
as claimed.

For the inductive step, suppose the implication holds for all $x \in \lists{A}$ and $v \in \nats$ for some $u$. Suppose further that $\nplus(\next(u),v) = \next(\length(x))$. We consider two possibilities for $x$; either $x = \nil$ or $x \neq \nil$. First suppose $x = \nil$. In this case we have
$$\begin{eqnarray*}
 &   & \at(x,\next(u)) \\
 & = & \at(\nil,\next(u)) \\
 & = & \ast \\
 & = & \at(\nil,v) \\
 & = & \at(\rev(\nil),v) \\
 & = & \at(\rev(x),v)
\end{eqnarray*}$$
as needed.

Suppose instead that $x = \cons(a,y)$. We now consider two possibilities for $u$; either $u = \zero$ or $u = \next(m)$ for some $m$. If $u = \zero$, we have $v = \length(x)$. In this case,
$$\begin{eqnarray*}
 &   & \at(x,\next(u)) \\
 & = & \at(\cons(a,y),\next(\zero)) \\
 & = & a \\
 & = & \head(\cons(a,\rev(y))) \\
 & = & \head(x) \\
 & = & \head(\rev(\rev(x))) \\
 & = & \at(\rev(x),\length(\rev(x))) \\
 & = & \at(\rev(x),\length(x)) \\
 & = & \at(\rev(x),v)
\end{eqnarray*}$$
as claimed. Finally, suppose $u = \next(m)$. Note that
$$\begin{eqnarray*}
 &   & \next(\nplus(u,v)) \\
 & = & \nplus(\next(u),v) \\
 & = & \next(\length(x)) \\
 & = & \next(\next(\length(y)),
\end{eqnarray*}$$
so that $\nplus(u,v) = \next(\length(y))$. In fact we have $\nleq(v,\length(y))$, since $u = \next(m)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \at(x,\next(u)) \\
 & = & \at(\cons(a,y),\next(\next(m))) \\
 & = & \at(y,\next(m)) \\
 & = & \at(y,u) \\
 & = & \at(\rev(y),v) \\
 & = & \at(\snoc(a,\rev(y)),v) \\
 & = & \at(\rev(\cons(a,y)),v) \\
 & = & \at(\rev(x),v)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally, $\at$ detects equality for lists.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, and let $x,y \in \lists{A}$. Then $x = y$ if and only if $\at(x,k) = \at(y,k)$ for all $k \in \nats$.
</p></div>

<div class="proof"><p>
The "only if" direction is clear. We show the "if" part by list induction on $x$. For the base case $x = \nil$, suppose we have $\at(x,k) = \at(y,k)$ for all $k \in \nats$. If $y = \cons(a,z)$ for some $z$, then we have
$$\begin{eqnarray*}
 &   & a \\
 & = & \at(\cons(a,z),\next(\zero)) \\
 & = & \at(y,\next(\zero)) \\
 & = & \at(x,\next(\zero)) \\
 & = & \ast,
\end{eqnarray*}$$
a contradiction. So $y = \nil = x$ as claimed.

For the inductive step, suppose the implication holds for some $x$, let $a \in A$, and suppose we have $\at(\cons(a,x),k) = \at(y,k)$ for all $k \in \nats$. If $y = \nil$, then again we have
$$\begin{eqnarray*}
 &   & a \\
 & = & \at(\cons(a,x),\next(\zero)) \\
 & = & \at(y,\next(\zero)) \\
 & = & \at(\nil,\next(\zero)) \\
 & = & \ast,
\end{eqnarray*}$$
a contradiction. Say $y = \cons(b,z)$. Now
$$\begin{eqnarray*}
 &   & a \\
 & = & \at(\cons(a,x),\next(\zero)) \\
 & = & \at(y,\next(\zero)) \\
 & = & \at(\cons(b,z),\next(\zero)) \\
 & = & b.
\end{eqnarray*}$$
Now we claim that $\at(x,k) = \at(z,k)$ for all $k$; to see this we consider two cases for $k$: either $k = \zero$ or $k = \next(m)$. If $k = \zero$ we have
$$\begin{eqnarray*}
 &   & \at(x,k) \\
 & = & \at(x,\zero) \\
 & = & \ast \\
 & = & \at(z,\zero) \\
 & = & \at(z,k).
\end{eqnarray*}$$
If $k = \next(m)$ we have
$$\begin{eqnarray*}
 &   & \at(x,k) \\
 & = & \at(x,\next(m)) \\
 & = & \at(\cons(a,x),\next(\next(m))) \\
 & = & \at(y,\next(\next(m))) \\
 & = & \at(\cons(b,z),\next(\next(m))) \\
 & = & \at(z,\next(m)) \\
 & = & \at(z,k).
\end{eqnarray*}$$
Thus $\at(x,k) = \at(z,k)$ for all $k$, and by the induction hypothesis we have $x = z$. Thus $\cons(a,x) = \cons(b,z) = y$ as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\at$.

> _test_at_nil :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (Nat n -> Bool)
> _test_at_nil z n =
>   testName "at(nil,k) == *" $
>   \m -> let
>     nil' = nil `withTypeOf` z
>   in
>     eq (at nil' m) Nothing
> 
> 
> _test_at_single :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (a -> Bool)
> _test_at_single z n =
>   testName "at(cons(a,nil),next(0)) == a" $
>   \a -> let
>     nil'  = nil  `withTypeOf` z
>     zero' = zero `withTypeOf` n
>   in
>     eq (at (cons a nil') (next zero')) (Just a)
> 
> 
> _test_at_double :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (a -> a -> Bool)
> _test_at_double z n =
>   testName "at(cons(a,cons(b,nil)),next(next(0))) == b" $
>   \a b -> let
>     nil'  = nil  `withTypeOf` z
>     zero' = zero `withTypeOf` n
>   in
>     eq (at (cons a (cons b nil')) (next (next zero'))) (Just b)
> 
> 
> _test_at_next_next_cons :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> a -> Nat n -> Bool)
> _test_at_next_next_cons z _ =
>   testName "at(cons(a,x),next(next(k))) == at(x,next(k))" $
>   \x a k -> eq (at (cons a x) (next (next k))) (at x (next k))
> 
> 
> _test_at_length_rev :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> Bool)
> _test_at_length_rev _ n =
>   testName "at(x,length(x)) == head(rev(x))" $
>   \x -> let
>     lx = length x `withTypeOf` n
>   in
>     eq (at x lx) (head (rev x))
> 
> 
> _test_at_range :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> Nat n -> Bool)
> _test_at_range _ n =
>   testName "leq(length(x),k) <==> at(x,next(k)) == *" $
>   \x k -> let
>     lx = length x `withTypeOf` Nat n
>   in
>     if and (not (isZero k)) (leq k lx)
>       then case at x k of
>         Just _  -> True
>         Nothing -> False
>       else eq (at x k) Nothing
> 
> 
> _test_at_snoc :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> a -> Nat n -> Bool)
> _test_at_snoc z n =
>   testName "leq(k,length(x)) ==> at(snoc(a,x),k) == at(x,k)" $
>   \x a k -> let
>     lx = length x `withTypeOf` Nat n
>   in
>     if leq k lx
>       then eq (at (snoc a x) k) (at x k)
>       else True
> 
> 
> _test_at_cat_left :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> ListOf t a -> Nat n -> Bool)
> _test_at_cat_left z n =
>   testName "leq(k,length(x))       ==> at(cat(x,y),k) == at(x,k)" $
>   \x y k -> let
>     lx = length x `withTypeOf` Nat n
>   in
>     if leq k lx
>       then eq (at (cat x y) k) (at x k)
>       else True
> 
> 
> _test_at_cat_right :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> ListOf t a -> Nat n -> Bool)
> _test_at_cat_right z n =
>   testName "leq(next(length(x)),k) ==> at(cat(x,y),k) == at(y,minus(k,length(x)))" $
>   \x y k -> let
>     lx = length x `withTypeOf` Nat n
>   in
>     if leq k lx
>       then True
>       else
>         let Just m = minus k lx in
>         eq (at (cat x y) k) (at y m)
> 
> 
> _test_at_rev :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> Nat n -> Bool)
> _test_at_rev z n =
>   testName "at(x,u) == at(rev(x),minus(next(length(x)),u))" $
>   \x u -> let 
>     lx = (length x) `withTypeOf` n
>   in
>     case minus (next (length x)) u of
>       Just v  -> eq (at x u) (at (rev x) v)
>       Nothing -> True

And the suite:

> -- run all tests for at
> _test_at ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName n, Natural n, Show n, Arbitrary n
>   , TypeName (t a), List t
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_at t n maxSize numCases = do
>   testLabel ("at: " ++ typeName t ++ " & " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_at_nil t n)
>   runTest args (_test_at_single t n)
>   runTest args (_test_at_double t n)
>   runTest args (_test_at_next_next_cons t n)
>   runTest args (_test_at_length_rev t n)
>   runTest args (_test_at_range t n)
>   runTest args (_test_at_snoc t n)
>   runTest args (_test_at_cat_left t n)
>   runTest args (_test_at_cat_right t n)
>   runTest args (_test_at_rev t n)

And ``main``:

> main_at :: IO ()
> main_at = do
>   _test_at (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_at (nil :: ConsList Unary) (zero :: Unary) 20 100
