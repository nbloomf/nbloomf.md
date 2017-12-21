---
title: Sublist
author: nbloomf
date: 2017-05-23
tags: arithmetic-made-difficult, literate-haskell
---

> module Sublist
>   ( sublist, _test_sublist, main_sublist
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll nail down what it means for one list to be a *sublist* of another. Intuitively, a sublist is "part of" some larger list; but there is some ambiguity here: does the sublist have to be contiguous in the larger list? For example, it seems clear that $$\langle b, c \rangle$$ should be considered a sublist of $$\langle a, b, c, d, e \rangle$$ while $$\langle e, g \rangle$$ should not. But what about $$\langle a, c \rangle,$$ or even $$\langle c, a \rangle$$ for that matter? First, lists are inherently ordered, so the "sublist" idea should reflect this -- sublists have to respect the order of their superlists. On the other hand, it is less crucial that sublists be contiguous in their superlists. Contiguous sublists are still interesting though (for reasons we'll see later), so we will single them out as infixes (analogous to prefixes and suffixes).

So we have two related but distinct concepts, sublists and infixes, that will need to be dealt with separately. We'll define two boolean functions, $\sublist$ and $\infix$, which detect when one list is a sublist or infix (respectively) of another. We'll start with $\sublist$. This function should have a signature like $$\lists{A} \times \lists{A} \rightarrow \bool.$$ Taking a cue from functions with similar signatures like $\zip$ and $\prefix$, we could try to define $\sublist$ as a right fold like $$\sublist(x,y) = \foldr{\varepsilon}{\varphi}(x)(y)$$ where $$\varepsilon : \lists{A} \rightarrow \bool$$ and $$\varphi : A \times (\lists{A} \rightarrow \bool) \rightarrow \lists{A} \rightarrow \bool.$$ But if we do this, assuming some reasonable behavior for $\sublist$, we get stuck! (Try it!) What happens is that the fold eats $x$, but when $x$ and $y$ are not nil but have different first items we need the recursion to un-eat the $x$ parameter. The fix is to instead fold on $y$ like $$\sublist(x,y) = \foldr{\varepsilon}{\varphi}(y,x).$$

Blah blah, define $\sublist$ like this.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times \bool^{\lists{A}} \rightarrow \bool^{\lists{A}}$ by $$\varphi(a,f)(x) = \left\{\begin{array}{ll} \btrue & \mathrm{if}\ x = \nil \\ \bif{\beq(a,b)}{f(w)}{f(x)} & \mathrm{if}\ x = \cons(b,w). \end{array}\right.$$ Now define $\sublist : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\sublist(x,y) = \foldr{\isnil}{\varphi}(y)(x).$$
</p></div>
</div>

We can translate the definition of $\sublist$ to Haskell:

> sublist' :: (List t, Equal a) => t a -> t a -> Bool
> sublist' x y = foldr isNil phi y x
>   where
>     phi a f w = case listShape w of
>       Nil      -> True
>       Cons b u -> if eq a b then f u else f w

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$ we have the following.

1. $\sublist(x,\nil) = \isnil(x)$.
2. $\sublist(\nil,y) = \btrue$.
3. $$\sublist(\cons(a,x),\cons(b,y)) = \left\{ \begin{array}{ll} \sublist(x,y) & \mathrm{if}\ a = b \\ \sublist(\cons(a,x),y) & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \sublist(x,\nil) \\
 & = & \foldr{\isnil}{\varphi}(\nil)(x) \\
 & = & \isnil(x)
\end{eqnarray*}$$
as claimed.
2. We consider two cases for $y$. If $y = \nil$, certainly $$\sublist(\nil,\nil) = \btrue$$ by (1). If $y = \cons(b,w)$, we have
$$\begin{eqnarray*}
 &   & \sublist(\nil,\cons(b,w)) \\
 & = & \foldr{\isnil}{\varphi}(\cons(b,w))(\nil) \\
 & = & \varphi(b,\foldr{\isnil}{\varphi}(w))(\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\isnil}{\varphi}(\cons(b,y))(\cons(a,x)) \\
 & = & \varphi(b,\foldr{\isnil}{\varphi}(y))(\cons(a,x)) \\
 & = & \bif{\beq(a,b)}{\foldr{\isnil}{\varphi}(y)(x)}{\foldr{\isnil}{\varphi}(y)(\cons(a,x))} \\
 & = & \bif{\beq(a,b)}{\sublist(x,y)}{\sublist(\cons(a,x),y)}
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> sublist :: (List t, Equal a) => t a -> t a -> Bool
> sublist x y = case listShape x of
>   Nil      -> True
>   Cons a u -> case listShape y of
>     Nil      -> False
>     Cons b v -> if eq a b
>       then sublist u v
>       else sublist x v

A lemma.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. Then $$\sublist(x,y) = \sublist(\cons(a,x),\cons(a,y)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),\cons(a,y)) \\
 & = & \bif{\beq(a,a)}{\sublist(x,y)}{\sublist(\cons(a,x),y)} \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Another lemma. This one seems like it should be obvious, but the only proof I could find was kind of complicated -- nested induction of two statements at once.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a,b \in A$ and $x,y \in \lists{A}$. Then we have the following.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cons(b,y)) = \btrue$.
2. If $\sublist(\cons(a,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
This proof is a little different: we will prove both (1) and (2) simultaneously by list induction on $x$. For the base case $x = \nil$, to see (1), note that for all $b \in A$ and $y \in \lists{A}$ we have $$\sublist(\nil,y) = \btrue = \sublist(\nil,\cons(b,y))$$ as needed. To see (2), note that $\sublist(\nil,y)$, so the implication holds regardless of the values of $a$ and $x$.

For the inductive step, suppose both (1) and (2) hold for all $a,b \in A$ and $y \in \lists{A}$ for some $x \in \lists{A}$, and let $c \in A$.

Now we claim that (1) holds with $x$ replaced by $\cons(c,x)$; that is, for all $b \in A$ and $y \in \lists{A}$, if $\sublist(\cons(c,x),y) = \btrue$ then $\sublist(\cons(c,x),\cons(b,y)) = \btrue$. To this end, suppose we have $\sublist(\cons(c,x),y) = \btrue$. Using part (2) of the induction hypothesis, we have $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),\cons(b,y)) \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \bif{\beq(c,b)}{\btrue}{\btrue} \\
 & = & \btrue
\end{eqnarray*}$$
as needed.

Next we claim that (2) holds with $x$ replaced by $\cons(c,x)$. That is, for all $a \in A$ and $y \in \lists{A}$, if $\sublist(\cons(a,\cons(c,x)),y) = \btrue$ then $\sublist(\cons(c,x),y) = \btrue$. We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,\cons(c,x)),y) \\
 & = & \sublist(\cons(a,\cons(c,x)),\nil) \\
 & = & \isnil(\cons(a,\cons(c,x))) \\
 & = & \bfalse;
\end{eqnarray*}$$
thus the implication (2) holds vacuously.

For the inductive step, suppose we have $y \in \lists{A}$ such that, for all $a \in A$, if $\sublist(\cons(a,\cons(c,x)),y) = \btrue$ then $\sublist(\cons(c,x),y) = \btrue$. Let $d \in A$, and suppose $$\sublist(\cons(a,\cons(c,x)),\cons(d,y)) = \btrue.$$

We consider two possibilities. If $a \neq d$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,\cons(c,x)),\cons(d,y)) \\
 & = & \sublist(\cons(a,\cons(c,x)),y).
\end{eqnarray*}$$
By the (nested) induction hypothesis, we have $$\sublist(\cons(c,x),y) = \btrue.$$ We established above that this implies $$\sublist(\cons(c,x),\cons(d,y)) = \btrue$$ as needed. Now suppose instead that $a = d$. Then
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,\cons(c,x)),\cons(d,y)) \\
 & = & \sublist(\cons(c,x),y).
\end{eqnarray*}$$
By part (2) of the (outer) induction hypothesis, we have $$\sublist(x,y) = \btrue.$$ Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),\cons(d,y)) \\
 & = & \bif{\beq(c,d)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \bif{\beq(c,d)}{\btrue}{\btrue} \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now $\sublist$ interacts with $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$, then $\nleq(\length(x),\length(y))$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, note that $\length(y) = \zero$. Now if
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(x,\nil) \\
 & = & \isnil(x),
\end{eqnarray*}$$
we have $x = \nil$, so that $\length(x) = \zero$. Thus
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\zero,\zero) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$ for some $y$, and let $b \in A$. We consider two cases for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\nil,\cons(b,y)) \\
 & = & \btrue,
\end{eqnarray*}$$
and furthermore
$$\begin{eqnarray*}
 &   & \nleq(\length(x),\length(\cons(b,y))) \\
 & = & \nleq(\length(\nil),\length(\cons(b,y))) \\
 & = & \nleq(\zero,\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose then that $x = \cons(a,u)$, and suppose further that $\sublist(x,\cons(b,y)) = \btrue$. We have two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y).
\end{eqnarray*}$$
By the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(u),\length(y)) \\
 & = & \nleq(\next(\length(u)),\next(\length(y))) \\
 & = & \nleq(\length(\cons(a,u)),\length(\cons(b,y))) \\
 & = & \nleq(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(\cons(a,u),y).
\end{eqnarray*}$$
By the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\cons(a,u)),\length(y)) \\
 & = & \nleq(\length(x),\length(y)) \\
 & = & \nleq(\length(x),\next(\length(y))) \\
 & = & \nleq(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\sublist$ is a partial order:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have the following.

1. $\sublist(x,x)$.
2. If $\sublist(x,y)$ and $\sublist(y,z)$, then $x = y$.
3. If $\sublist(x,y)$ and $\sublist(y,z)$, then $\sublist(x,z)$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, certainly $$\sublist(\nil,\nil) = \btrue.$$ For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),\cons(a,x)) \\
 & = & \bif{\beq(a,a)}{\sublist(x,x)}{\sublist(\cons(a,x),x)} \\
 & = & \sublist(x,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(y,x) \\
 & = & \sublist(y,\nil) \\
 & = & \isnil(y),
\end{eqnarray*}$$
so that $y = \nil = x$ as claimed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. We now consider two possibilities for $y$. If $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),y) \\
 & = & \sublist(\cons(a,x),\nil) \\
 & = & \isnil(\cons(a,x)) \\
 & = & \bfalse.
\end{eqnarray*}$$
Thus the implication holds vacuously. Suppose instead that $y = \cons(b,v)$, and suppose further that $\sublist(\cons(a,x),\cons(b,v))$ and $\sublist(\cons(b,v),\cons(a,x))$ are both $\btrue$. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(a,x)) \\
 & = & \sublist(\cons(b,v),x) \\
 & = & \sublist(y,x).
\end{eqnarray*}$$
But now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\cons(a,x)),\length(y)) \\
 & = & \nleq(\next(\length(x)),\length(y)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(y),\length(x));
\end{eqnarray*}$$
by transitivity, we thus also have $$\nleq(\next(\length(x)),\length(x)),$$ a contradiction. So in fact $a = b$. Thus we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(a,x)) \\
 & = & \sublist(v,x)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,x),\cons(b,v)) \\
 & = & \sublist(x,v),
\end{eqnarray*}$$
so that (by the induction hypothesis) we have $x = v$, and so
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cons(b,v) \\
 & = & y
\end{eqnarray*}$$
as needed.
3. We proceed by list induction on $z$. For the base case $z = \nil$, note that if $\sublist(y,z) = \btrue$ we have $y = \nil$, and then if $\sublist(x,y) = \btrue$ we also have $x = \nil$. In particular, $\sublist(x,z) = \btrue$ as needed. For the inductive step, suppose the implication holds for all $x$ and $y$ for some $z$, and let $c \in A$. Suppose further that $\sublist(x,y)$ and $\sublist(y,\cons(c,z))$. We consider two cases for $y$. If $y = \nil$, note that $x = \nil$, so we have $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $y = \cons(b,v)$. If $b \neq c$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(c,z)) \\
 & = & \sublist(\cons(b,v),z);
\end{eqnarray*}$$
by the inductive hypothesis, we have $\sublist(x,z)$, so that $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $b = c$; then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(b,v),\cons(c,z)) \\
 & = & \sublist(v,z).
\end{eqnarray*}$$
We consider two cases for $x$; if $x = \nil$, then $\sublist(x,\cons(c,z))$ as claimed. Suppose instead that $x = \cons(a,u)$. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,u),\cons(b,v)) \\
 & = & \sublist(\cons(a,u),v),
\end{eqnarray*}$$
and by the inductive hypothesis, $\sublist(x,z)$, so that $\sublist(x,\cons(c,z))$ as claimed. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cons(a,u),\cons(b,v)) \\
 & = & \sublist(u,v).
\end{eqnarray*}$$
By the inductive hypothesis, $\sublist(u,z)$, so that $\sublist(x,\cons(c,z))$ as claimed.
</p></div>
</div>

$\sublist$ interacts with $\snoc$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. We have the following.

1. $\sublist(\snoc(a,x),\nil) = \bfalse$.
2. $\sublist(x,y) = \sublist(\snoc(a,x),\snoc(a,y))$.
</p></div>

<div class="proof"><p>
1. Note that $\snoc(a,x) = \cons(b,u)$ for some $b \in A$ and $u \in \lists{A}$; then
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\nil) \\
 & = & \sublist(\cons(b,u),\nil) \\
 & = & \isnil(\cons(b,u)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that $\sublist(x,y) = \btrue$. We show that $\sublist(\snoc(a,\nil),\snoc(a,y)) = \btrue$ by list induction on $y$. For the base case $y = \nil$, we have $$\sublist(\snoc(a,\nil),\snoc(a,\nil)) = \btrue$$ by reflexivity. For the inductive step (on $y$), suppose the equality holds for some $y$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\nil),\snoc(a,\cons(b,y))) \\
 & = & \sublist(\cons(a,\nil),\cons(b,\snoc(a,y))) \\
 & = & \bif{\beq(a,b)}{\sublist(\nil,\snoc(a,y))}{\sublist(\cons(a,\nil),\snoc(a,y))} \\
 & = & \bif{\beq(a,b)}{\btrue}{\sublist(\snoc(a,\nil),\snoc(a,y))} \\
 & = & \bif{\beq(a,b)}{\btrue}{\btrue} \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step (on $x$), suppose the equality holds for some $x$ and let $c \in A$. We need to show that $$\sublist(\cons(c,x),y) = \sublist(\snoc(a,\cons(c,x)),\snoc(a,y))$$ for all $y$; we again proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(c,x),y) \\
 & = & \sublist(\cons(c,x),\nil) \\
 & = & \isnil(\cons(c,x)) \\
 & = & \bfalse,
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\cons(c,x)),\snoc(a,y)) \\
 & = & \sublist(\snoc(a,\cons(c,x)),\snoc(a,\nil)) \\
 & = & \sublist(\cons(c,\snoc(a,x)),\cons(a,\nil)) \\
 & = & \bif{\beq(c,a)}{\sublist(\snoc(a,x),\nil)}{\sublist(\cons(c,\snoc(a,x)),\nil)} \\
 & = & \bif{\beq(c,a)}{\bfalse}{\bfalse} \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. For the inductive step (on $y$), suppose we have $$\sublist(\cons(c,x),y) = \sublist(\snoc(a,\cons(c,x)),\snoc(a,y))$$ for some $y$, and let $b \in A$. Using both the outer and nested inductive hypotheses we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,\cons(c,x)),\snoc(a,\cons(b,y))) \\
 & = & \sublist(\cons(c,\snoc(a,x)),\cons(b,\snoc(a,y))) \\
 & = & \bif{\beq(c,b)}{\sublist(\snoc(a,x),\snoc(a,y))}{\sublist(\cons(c,\snoc(a,x)),\snoc(a,y))} \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\snoc(a,\cons(c,x)),\snoc(a,y))} \\
 & = & \bif{\beq(c,b)}{\sublist(x,y)}{\sublist(\cons(c,x),y)} \\
 & = & \sublist(\cons(c,x),\cons(b,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\sublist$ interacts with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,u,v \in \lists{A}$.

1. $\sublist(x,y) = \sublist(\cat(u,x),\cat(u,y))$.
2. $\sublist(x,y) = \sublist(\cat(x,u),\cat(y,u))$.
3. If $\sublist(x,u)$ and $\sublist(y,v)$, then $\sublist(\cat(x,y),\cat(u,v))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $u$. For the base case $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\cat(u,x),\cat(u,y)) \\
 & = & \sublist(\cat(\nil,x),\cat(\nil,y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $u$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \sublist(x,y) \\
 & = & \sublist(\cat(u,x),\cat(u,y)) \\
 & = & \sublist(\cons(a,\cat(u,x)),\cons(a,\cat(u,y))) \\
 & = & \sublist(\cat(\cons(a,u),x),\cat(\cons(a,u),y))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $u$. For the base case $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\cat(x,u),\cat(y,u)) \\
 & = & \sublist(\cat(x,\nil),\cat(y,\nil)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $u$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \sublist(x,y) \\
 & = & \sublist(\snoc(a,x),\snoc(a,y)) \\
 & = & \sublist(\cat(\snoc(a,x),u),\cat(\snoc(a,y),u)) \\
 & = & \sublist(\cat(x,\cons(a,u)),\cat(y,\cons(a,u)))
\end{eqnarray*}$$
as needed.
3. If $\sublist(x,u) = \btrue$, then $\sublist(\cat(x,y),\cat(u,y)) = \btrue$. Similarly, if $\sublist(y,v) = \btrue$, then $\sublist(\cat(u,y),\cat(u,v)) = \btrue$. By transitivity, we have $$\sublist(\cat(x,y),cat(u,v)) = \btrue$$ as claimed.
</p></div>
</div>

Another lemma.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \left\{ \begin{array}{ll} \sublist(x,y) & \mathrm{if}\ \beq(a,b) \\ \sublist(\snoc(a,x),y) & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
We've already seen that $$\sublist(\snoc(a,x),\snoc(a,y)) = \sublist(x,y).$$ So it suffices to show that if $a \neq b$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \sublist(\snoc(a,x),y).$$ We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),y) \\
 & = & \sublist(\snoc(a,x),\nil) \\
 & = & \isnil(\snoc(a,x)) \\
 & = & \bfalse.
\end{eqnarray*}$$
We will now show that $\sublist(\snoc(a,x),\snoc(b,\nil)) = \bfalse$ by considering two cases for $x$. If $x = nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\nil)) \\
 & = & \sublist(\snoc(a,\nil),\snoc(b,\nil)) \\
 & = & \sublist(\cons(a,\nil),\cons(b,\nil)) \\
 & = & \sublist(\cons(a,\nil),\nil) \\
 & = & \isnil(\cons(a,\nil)) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. If $x = \cons(c,u)$ and $\sublist(\snoc(a,x),\snoc(b,\nil)) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\length(\snoc(a,x)),\length(\snoc(b,\nil)) \\
 & = & \nleq(\next(\length(x)),\next(\length(\nil))) \\
 & = & \nleq(\next(\length(\cons(c,u))),\next(\zero)) \\
 & = & \nleq(\next(\next(\length(u))),\next(\zero)) \\
 & = & \bfalse,
\end{eqnarray*}$$
a contradiction.

Now for the inductive step, suppose the equality holds for some $y$. That is, for all $a \neq b$ and all $x$ we have $$\sublist(\snoc(a,x),\snoc(b,y)) = \sublist(\snoc(a,x),y).$$ Let $d \in A$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\snoc(a,\nil),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\cons(a,\nil),\cons(d,\snoc(b,y))) \\
 & = & \bif{\beq(a,d)}{\sublist(\nil,\snoc(b,y))}{\sublist(\cons(a,\nil),\snoc(b,y))} \\
 & = & \bif{\beq(a,d)}{\btrue}{\sublist(\snoc(a,\nil),\snoc(b,y))} \\
 & = & \bif{\beq(a,d)}{\btrue}{\sublist(\snoc(a,\nil),y)} \\
 & = & \bif{\beq(a,d)}{\sublist(\nil,y)}{\sublist(\cons(a,\nil),y)} \\
 & = & \sublist(\cons(a,\nil),\cons(d,y)) \\
 & = & \sublist(\snoc(a,\nil),\cons(d,y))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(c,u)$. Now we have
$$\begin{eqnarray*}
 &   & \sublist(\snoc(a,x),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\snoc(a,\cons(c,u)),\snoc(b,\cons(d,y))) \\
 & = & \sublist(\cons(c,\snoc(a,u)),\cons(d,\snoc(b,y))) \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),\snoc(b,y))}{\sublist(\cons(c,\snoc(a,u)),\snoc(b,y))} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\snoc(a,\cons(c,u)),\snoc(b,y))} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\snoc(a,\cons(c,u)),y)} \\
 & = & \bif{\beq(c,d)}{\sublist(\snoc(a,u),y)}{\sublist(\cons(c,\snoc(a,u)),y)} \\
 & = & \sublist(\cons(c,\snoc(a,u)),\cons(d,y)) \\
 & = & \sublist(\snoc(a,\cons(c,u)),\cons(d,y)) \\
 & = & \sublist(\snoc(a,x),\cons(d,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\sublist$ interacts with $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\sublist(x,y) = \sublist(\rev(x),\rev(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,y) \\
 & = & \sublist(x,\nil) \\
 & = & \isnil(x) \\
 & = & \isnil(\rev(x)) \\
 & = & \sublist(\rev(x),\nil) \\
 & = & \sublist(\rev(x),\rev(\nil)) \\
 & = & \sublist(\rev(x),\rev(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $y$ and let $b \in A$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\nil,\cons(b,y)) \\
 & = & \btrue \\
 & = & \sublist(\nil,\rev(\cons(b,y))) \\
 & = & \sublist(\rev(\nil),\rev(\cons(b,y))) \\
 & = & \sublist(\rev(x),\rev(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,w)$. Then we have
$$\begin{eqnarray*}
 & = & \sublist(\rev(x),\rev(\cons(b,y))) \\
 & = & \sublist(\rev(\cons(a,w)),\rev(\cons(b,y))) \\
 & = & \sublist(\snoc(a,\rev(w)),\snoc(b,\rev(y))) \\
 & = & \bif{\beq(a,b)}{\sublist(\rev(w),\rev(y))}{\sublist(\snoc(a,\rev(w)),\rev(y))} \\
 & = & \bif{\beq(a,b)}{\sublist(w,y)}{\sublist(\rev(\cons(a,w)),\rev(y))} \\
 & = & \bif{\beq(a,b)}{\sublist(w,y)}{\sublist(\cons(a,w),y)} \\
 & = & \sublist(\cons(a,w),\cons(b,y)) \\
 & = & \sublist(x,\cons(b,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

More $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. Then we have the following.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\snoc(a,y)) = \btrue$.
2. If $\sublist(\snoc(a,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
1. Suppose $\sublist(x,y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(\rev(x),\cons(a,\rev(y))) \\
 & = & \sublist(\rev(x),\rev(\snoc(a,y))) \\
 & = & \sublist(x,\snoc(a,y))
\end{eqnarray*}$$
as claimed.
2. Suppose $\sublist(\snoc(a,x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\snoc(a,x),y) \\
 & = & \sublist(\rev(\snoc(a,x)),\rev(y)) \\
 & = & \sublist(\cons(a,\rev(x)),\rev(y)) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And again.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x,y,z \in \lists{A}$.

1. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cat(z,y)) = \btrue$.
2. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cat(y,z)) = \btrue$.
3. If $\sublist(\cat(z,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.
4. If $\sublist(\cat(x,z),y) = \btrue$, then $\sublist(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $z$. For the base case $z = \nil$, suppose $\sublist(x,y) = \btrue$. Then
$$\begin{eqnarray*}
 &   & \sublist(x,\cat(z,y)) \\
 & = & \sublist(x,\cat(\nil,y)) \\
 & = & \sublist(x,y) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $z$ and let $a \in A$. Suppose further that $\sublist(x,y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(x,\cat(z,y)) \\
 & = & \sublist(x,\cons(a,\cat(z,y))) \\
 & = & \sublist(x,\cat(\cons(a,z),y))
\end{eqnarray*}$$
as needed.
2. Suppose $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,y) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(\rev(x),\cat(\rev(z),\rev(y))) \\
 & = & \sublist(\rev(x),\rev(\cat(y,z))) \\
 & = & \sublist(x,\cat(y,z))
\end{eqnarray*}$$
as claimed.
3. We proceed by list induction on $z$. For the base case $z = \nil$, suppose $\sublist(\cat(z,x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(z,x),y) \\
 & = & \sublist(\cat(\nil,x),y) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$ and $y$ for some $z$ and let $a \in A$. Suppose further that $\sublist(\cat(\cons(a,z),x),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(\cons(a,z),x),y) \\
 & = & \sublist(\cons(a,\cat(z,x)),y) \\
 & = & \sublist(\cat(z,x),y) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
4. Suppose $\sublist(\cat(x,z),y) = \btrue$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(\cat(x,z),y) \\
 & = & \sublist(\rev(\cat(x,z)),\rev(y)) \\
 & = & \sublist(\cat(\rev(z),\rev(x)),\rev(y)) \\
 & = & \sublist(\rev(x),\rev(y)) \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\sublist$ and $\map$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $x,y \in \lists{A}$ and $f : A \rightarrow B$ injective. If $\sublist(x,y) = \btrue$, then $\sublist(\map(f)(x),\map(f)(y)) = \btrue$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, suppose $\sublist(x,y) = \btrue$. Then in fact $x = \nil$. In this case we have
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(x),\map(f)(y)) \\
 & = & \sublist(\map(f)(\nil),\map(f)(\nil)) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $x$ for some $y$ and let $b \in A$. Suppose further that $\sublist(x,\cons(a,y)) = \btrue$. We have two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(x),\map(f)(\cons(a,y))) \\
 & = & \sublist(\map(f)(\nil),\map(f)(\cons(a,y))) \\
 & = & \sublist(\nil,\map(f)(\cons(a,y))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,u)$. Note that if $f(a) = f(b)$ then $a = b$ (since $f$ is injective) and we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y),
\end{eqnarray*}$$
and if $f(a) \neq f(b)$, then $a \neq b$ (since $f$ is injective), and we have
$$\begin{eqnarray*}
 & = & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(\cons(a,u),y) \\
 & = & \sublist(x,y).
\end{eqnarray*}$$
In either case, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \sublist(\map(f)(x),\map(f)(\cons(b,y))) \\
 & = & \sublist(\map(f)(\cons(a,u)),\map(f)(\cons(b,y))) \\
 & = & \sublist(\cons(f(a),\map(f)(u)),\cons(f(b),\map(f)(y))) \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(\map(f)(u),\map(f)(y))}{\sublist(\cons(f(a),\map(f)(u)),\map(f)(y)} \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(\map(f)(u),\map(f)(y))}{\sublist(\map(f)(\cons(a,u)),\map(f)(y)} \\
 & = & \bif{\beq(f(a),f(b))}{\sublist(\map(f)(u),\map(f)(y))}{\sublist(\map(f)(x),\map(f)(y)} \\
 & = & \bif{\beq(f(a),f(b))}{\btrue}{\btrue} \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\sublist$ and $\filter$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, let $p : A \rightarrow \bool$, and let $x \in \lists{A}$. Then we have $$\sublist(\filter(p,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,x),x) \\
 & = & \sublist(\filter(p,\nil),\nil) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $p$ for some $x$ and let $a \in A$. We consider two possibilities. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,\cons(a,x)),\cons(a,x)) \\
 & = & \sublist(\bif{p(a)}{\cons(a,\filter(p,x)}{\filter(p,x)},\cons(a,x)) \\
 & = & \sublist(\cons(a,\filter(p,x)),\cons(a,x)) \\
 & = & \sublist(\filter(p,x),x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, note that $$\sublist(\filter(p,x),x) = \btrue,$$ so that
$$\begin{eqnarray*}
 &   & \sublist(\filter(p,\cons(a,x)),\cons(a,x)) \\
 & = & \sublist(\bif{p(a)}{\cons(a,\filter(p,x)}{\filter(p,x)},\cons(a,x)) \\
 & = & \sublist(\filter(p,x),\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally, $\sublist$ interacts with $\any$ and $\all$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, let $x,y \in \lists{A}$, and let $p : A \rightarrow \bool$. If $\sublist(x,y)= \btrue$, then we have the following.

1. If $\all(p,y) = \btrue$ then $\all(p,x) = \btrue$.
2. If $\any(p,x) = \btrue$ then $\any(p,y) = \btrue$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $y$. For the base case $y = \nil$, since $\sublist(x,y) = \btrue$ we have $x = \nil$. Now $$\all(p,y) = \all(p,\nil) = \btrue$$ and $$\all(p,x) = \all(p,\nil) = \btrue$$ as needed. For the inductive step, suppose the result holds for all $x$ for some $y$, and let $b \in A$. Suppose $\sublist(x,\cons(b,y)) = \btrue$, and further suppose that $\all(p,\cons(b,y)) = \btrue$. In particular, note that $p(b) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, note that $$\all(p,x) = \all(p,\nil) = \btrue,$$ so the implication holds regardless of $y$. Suppose instead that $x = \cons(a,u)$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \bif{\beq(a,b)}{\sublist(u,y)}{\sublist(\cons(a,u),y)} \\
 & = & \bif{\beq(a,b)}{\all(p,u)}{\all(p,\cons(a,u))} \\
 & = & \bif{\beq(a,b)}{\all(p,\cons(a,u))}{\all(p,\cons(a,u))} \\
 & = & \all(p,\cons(a,u)) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as needed.
2. We prove this implication by contraposition. Suppose $\any(p,y) = \bfalse$; then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \bnot(\bfalse) \\
 & = & \bnot(\any(p,y)) \\
 & = & \all(\bnot \circ p, y).
\end{eqnarray*}$$
Using (1), we thus have
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \bnot(\btrue) \\
 & = & \bnot(\all(\bnot \circ p,x)) \\
 & = & \bnot(\bnot(\any(p,x))) \\
 & = & \any(p,x)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

One more.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$, then $\beq(\cons(a,y),x) = \bfalse$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that $$\sublist(x,y) = \sublist(\nil,y) = \btrue$$ and
$$\begin{eqnarray*}
 &   & \beq(\cons(a,y),x) \\
 & = & \beq(\cons(a,y),\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $a$ and $y$ for some $x$ and let $b \in A$. We now consider two possibilities for $y$. If $y = \nil$, note that $$\sublist(\cons(b,x),y) = \sublist(\cons(b,x),\nil) = \bfalse,$$ so the implication holds vacuously. Suppose instead that $y = \cons(c,w)$. Suppose further that $\sublist(\cons(b,x),y) = \btrue$. We consider two possibilities. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,y),\cons(b,w)) \\
 & = & \beq(\cons(a,\cons(c,w)),\cons(b,x)) \\
 & = & \band(\beq(a,b),\beq(\cons(c,w),x)) \\
 & = & \band(\bfalse,\beq(\cons(c,w),x)) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. Suppose instead that $a = b$. We now consider two possibilities. If $b = c$, then since $\sublist(\cons(b,x),\cons(c,w)) = \btrue$, we have $\sublist(x,w) = \btrue$. Using the inductive hypothesis on $x$ we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,\cons(c,w)),\cons(b,x)) \\
 & = & \band(\beq(a,b),\beq(\cons(c,w),x)) \\
 & = & \band(\btrue,\beq(\cons(c,w),x)) \\
 & = & \beq(\cons(c,w),x) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. Suppose instead that $b \neq c$. Now since $\sublist(\cons(b,x),\cons(c,w)) = \btrue$, we have $\sublist(\cons(b,x),w) = \btrue$, and thus $\sublist(x,w) = \btrue$. Using the inductive hypothesis on $x$, we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,\cons(c,w)),\cons(b,x)) \\
 & = & \band(\beq(a,b),\beq(\cons(c,w),x)) \\
 & = & \band(\btrue,\beq(\cons(c,w),x)) \\
 & = & \beq(\cons(c,w),x) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\sublist$:

> _test_sublist_alt :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_sublist_alt _ =
>   testName "sublist'(x,y) == sublist(x,y)" $
>   \x y -> eq (sublist' x y) (sublist x y)
> 
> 
> _test_sublist_cons :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cons _ =
>   testName "sublist(x,y) == sublist(cons(a,x),cons(a,y))" $
>   \a x y -> eq (sublist (cons a x) (cons a y)) (sublist x y)
> 
> 
> _test_sublist_cons_left :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cons_left _ =
>   testName "sublist(cons(a,x),y) ==> sublist(x,y)" $
>   \a x y -> if sublist (cons a x) y
>     then sublist x y
>     else True
> 
> 
> _test_sublist_cons_right :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cons_right _ =
>   testName "sublist(x,y) ==> sublist(x,cons(a,y))" $
>   \a x y -> if sublist x y
>     then sublist x (cons a y)
>     else True
> 
> 
> _test_sublist_reflexive :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_sublist_reflexive _ =
>   testName "sublist(x,x) == true" $
>   \x -> eq (sublist x x) True
> 
> 
> _test_sublist_antisymmetric :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_sublist_antisymmetric _ =
>   testName "sublist(x,y) & sublist(y,x) ==> eq(x,y)" $
>   \x y -> eq (and (sublist x y) (sublist y x)) (eq x y)
> 
> 
> _test_sublist_transitive :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_transitive _ =
>   testName "sublist(x,y) & sublist(y,z) ==> sublist(x,z)" $
>   \x y z -> if and (sublist x y) (sublist y z)
>     then sublist x z
>     else True
> 
> 
> _test_sublist_snoc_nil :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> Bool)
> _test_sublist_snoc_nil _ =
>   testName "sublist(snoc(a,x),nil) == false" $
>   \a x -> eq (sublist (snoc a x) nil) False
> 
> 
> _test_sublist_rev :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_sublist_rev _ =
>   testName "sublist(x,y) == sublist(rev(x),rev(y))" $
>   \x y -> eq (sublist x y) (sublist (rev x) (rev y))
> 
> 
> _test_sublist_cat_left :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cat_left _ =
>   testName "sublist(x,y) ==> sublist(cat(u,x),cat(u,y))" $
>   \x y u -> if sublist x y
>     then sublist (cat u x) (cat u y)
>     else True
> 
> 
> _test_sublist_cat_right :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cat_right _ =
>   testName "sublist(x,y) ==> sublist(cat(x,u),cat(y,u))" $
>   \x y u -> if sublist x y
>     then sublist (cat x u) (cat y u)
>     else True
> 
> 
> _test_sublist_cat :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool)
> _test_sublist_cat _ =
>   testName "sublist(x,y) & sublist(u,v) ==> sublist(cat(x,u),cat(y,v))" $
>   \x y u v -> if and (sublist x y) (sublist u v)
>     then sublist (cat x u) (cat y v)
>     else True

And the suite:

> -- run all tests for sublist
> _test_sublist ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_sublist t maxSize numCases = do
>   testLabel ("sublist: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_sublist_alt t)
>   runTest args (_test_sublist_cons t)
>   runTest args (_test_sublist_cons_left t)
>   runTest args (_test_sublist_cons_right t)
>   runTest args (_test_sublist_reflexive t)
>   runTest args (_test_sublist_antisymmetric t)
>   runTest args (_test_sublist_transitive t)
>   runTest args (_test_sublist_snoc_nil t)
>   runTest args (_test_sublist_rev t)
>   runTest args (_test_sublist_cat_left t)
>   runTest args (_test_sublist_cat_right t)
>   runTest args (_test_sublist_cat t)

And ``main``:

> main_sublist :: IO ()
> main_sublist = do
>   _test_sublist (nil :: ConsList Bool)  30 200
>   _test_sublist (nil :: ConsList Unary) 30 200
