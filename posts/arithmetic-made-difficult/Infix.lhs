---
title: Infix
author: nbloomf
date: 2017-05-24
tags: arithmetic-made-difficult, literate-haskell
slug: infix
---

> module Infix
>   ( isInfix, _test_isInfix, main_isInfix
>   ) where
> 
> import Prelude ()
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Sublist

Today we'll nail down ``infix``, a variant on ``sublist``.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\infix : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\infix(x,y) = \any(\prefix(x,-))(\tails(y)).$$

In Haskell:

> isInfix :: (List t, Equal a) => t a -> t a -> Bool
> isInfix x y = any (prefix x) (tails y)

</p></div>
</div>

(``infix`` is a reserved word in Haskell, so we'll call this function ``isInfix``.)

(@@@)

The following result suggests another implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\infix(\nil,y) = \btrue$.
2. $\infix(\cons(a,x),\nil) = \bfalse$.
3. $\infix(x,\cons(b,y)) = \bor(\prefix(x,\cons(b,y)),\infix(x,y))$.
</p></div>

<div class="proof"><p>
1. Note that, since $\tails(y) \neq \nil$, we have
$$\begin{eqnarray*}
 &   & \infix(\nil,y) \\
 & = & \any(\prefix(\nil,-),\tails(y)) \\
 & = & \any(\const(\btrue),\tails(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \infix(\cons(a,x),\nil) \\
 & = & \any(\prefix(\cons(a,x),-),\tails(\nil)) \\
 & = & \any(\prefix(\cons(a,x),-),\cons(\nil,\nil)) \\
 & = & \bor(\prefix(\cons(a,x),\nil),\any(\prefix(\cons(a,x),-),\nil)) \\
 & = & \bor(\bfalse,\bfalse) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \infix(x,\cons(b,y)) \\
 & = & \any(\prefix(x,-),\tails(\cons(b,y))) \\
 & = & \any(\prefix(x,-),\cons(\cons(b,y),\tails(y))) \\
 & = & \bor(\prefix(x,\cons(b,y)),\any(\prefix(x,-),\tails(y))) \\
 & = & \bor(\prefix(x,\cons(b,y)),\infix(x,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\infix$ is reflexive:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $x \in \lists{A}$, then $\infix(x,x) = \btrue$.
</p></div>

<div class="proof"><p>
We consider two cases for $x$. If $x = \nil$, we have $$\infix(x,x) = \infix(\nil,\nil) = \btrue$$ as claimed. If $x = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \infix(x,x) \\
 & = & \infix(x,\cons(a,u)) \\
 & = & \bor(\prefix(x,\cons(a,u)),\infix(x,u)) \\
 & = & \bor(\prefix(x,x),\infix(x,u)) \\
 & = & \bor(\btrue,\infix(x,u)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. 
</p></div>
</div>

$\infix$ interacts with $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y \in \lists{A}$.

1. $\infix(x,\cat(y,x)) = \btrue$.
2. $\infix(x,\cat(x,y)) = \btrue$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $y$. For the base case, note that
$$\begin{eqnarray*}
 &   & \infix(x,\cat(y,x)) \\
 & = & \infix(x,\cat(\nil,x)) \\
 & = & \infix(x,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $y$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \infix(x,\cat(\cons(b,y),x) \\
 & = & \infix(x,\cons(b,\cat(x,y))) \\
 & = & \bor(\prefix(x,\cons(b,\cat(x,y))),\infix(x,\cat(x,y))) \\
 & = & \bor(\prefix(x,\cons(b,\cat(x,y))),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. We consider two possibilities for $x$. If $x = \nil$, we have $$\infix(x,\cat(x,y)) = \infix(\nil,\cat(x,y)) = \btrue$$ as claimed. Suppose then that $x = \cons(a,u)$. Then we have
$$\begin{eqnarray*}
 &   & \infix(x,\cat(x,y)) \\
 & = & \infix(x,\cat(\cons(a,u),y)) \\
 & = & \infix(x,\cons(a,\cat(u,y))) \\
 & = & \bor(\prefix(x,\cons(a,\cat(u,y))),\infix(x,\cat(u,y))) \\
 & = & \bor(\prefix(x,\cat(\cons(a,u),y)),\infix(x,\cat(u,y))) \\
 & = & \bor(\prefix(x,\cat(x,y)),\infix(x,\cat(u,y))) \\
 & = & \bor(\btrue,\infix(x,\cat(u,y))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Prefixes and suffixes are also infixes:

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. The following hold for all $x,y \in \lists{A}$.

1. If $\prefix(x,y) = \btrue$, then $\infix(x,y) = \btrue$.
2. If $\suffix(x,y) = \btrue$, then $\infix(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
1. Recall that $\prefix(x,y) = \btrue$ if and only if $y = \cat(x,z)$ for some $z$. Then $$\infix(x,y) = \infix(x,\cat(x,z)) = \btrue$$ as claimed.
2. Recall that $\suffix(x,y) = \btrue$ if and only if $y = \cat(z,x)$ for some $z$. Then $$\infix(x,y) = \infix(x,\cat(z,x)) = \btrue$$ as claimed.
</p></div>
</div>

$\infix$ interacts with $\cons$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y \in \lists{A}$.

1. If $\infix(x,y) = \btrue$, then $\infix(x,\cons(a,y)) = \btrue$.
2. If $\infix(x,y) = \btrue$, then $\infix(x,\snoc(a,y)) = \btrue$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\infix(x,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $y$. For the base case $y = \nil$, note that we must have $x = \nil$. Now $$\infix(x,\snoc(a,y)) = \infix(\nil,\snoc(a,y)) = \btrue$$ as needed. For the inductive step, suppose the implication holds for some $y$ and let $b \in A$. Suppose further that $\infix(x,\cons(b,y)) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(b,y)),\infix(x,y)).
\end{eqnarray*}$$
We have two possibilities. First suppose $\prefix(x,\cons(b,y)) = \btrue$. Then $\prefix(x,\snoc(a,\cons(a,y))) = \btrue$, and so $\infix(x,\snoc(a,\cons(b,y))$ as needed. Suppose instead that $\infix(x,y) = \btrue$. By the inductive hypothesis we have $$\infix(x,\snoc(a,y)) = \btrue,$$ and by the previous result we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,\cons(b,\snoc(a,y))) \\
 & = & \infix(x,\snoc(a,\cons(b,y)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y \in \lists{A}$.

1. If $\infix(x,y) = \btrue$, then $\infix(x,\cat(y,z)) = \btrue$.
2. If $\infix(x,y) = \btrue$, then $\infix(x,\cat(z,y)) = \btrue$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $z$. For the base case $z = \nil$, we have $$\infix(x,\cat(y,z)) = \infix(x,\cat(y,\nil)) = \infix(x,y) = \btrue.$$ For the inductive step, suppose the implication holds for some $z$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,y) \\
 & = & \infix(x,\snoc(a,y)) \\
 & = & \infix(x,\cat(\snoc(a,y),z)) \\
 & = & \infix(x,\cat(y,\cons(a,z)))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $z$. For the base case $z = \nil$ we have $$\infix(x,\cat(z,y)) = \infix(x,\cat(\nil,y)) = \infix(x,y) = \btrue$$ as needed. For the inductive step, suppose the implication holds for some $z$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,y) \\
 & = & \infix(x,\cat(z,y)) \\
 & = & \infix(x,\cons(a,\cat(z,y))) \\
 & = & \infix(x,\cat(\cons(a,z),y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now $\infix$ detects two-sided $\cat$-factorizations:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Then the following hold for all $x,y \in \lists{A}$.

1. $\infix(x,\cat(u,\cat(x,v))) = \btrue$ for all $u,v \in \lists{A}$.
2. If $\infix(x,y) = \btrue$, then $y = \cat(u,\cat(x,v))$ for some $u,v \in \lists{A}$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,x) \\
 & = & \infix(x,\cat(x,v)) \\
 & = & \infix(x,\cat(u,\cat(x,v)))
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $y$. For the base case $y = \nil$, if $\infix(x,y) = \btrue$, we have $x = \nil$. Now $x = y$, so that $y = \cat(\nil,\cat(x,\nil))$ as needed. For the inductive step, suppose the implication holds for some $y$ and let $a \in A$. Suppose further that $\infix(x,\cons(a,y)) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\infix(x,y)).
\end{eqnarray*}$$
We have two possibilities. If $\prefix(x,\cons(a,y)) = \btrue$, then $\cons(a,y) = \cat(x,z)$ for some $z$; now $$\cons(a,y) = \cat(\nil,\cat(x,z))$$ as needed. Suppose instead that $\infix(x,y) = \btrue$. By the inductive hypothesis we have $y = \cat(u,\cat(x,v))$ for some $u$ and $v$, so that
$$\begin{eqnarray*}
 &   & \cons(a,y) \\
 & = & \cons(a,\cat(u,\cat(x,v))) \\
 & = & \cat(\cons(a,u),\cat(x,v))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\infix$ interacts with $\snoc$ and $\rev$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. We have the following.

1. $\infix(\rev(x),\rev(y)) = \infix(x,y)$.
2. $\infix(\snoc(a,x),\nil) = \bfalse$.
3. $\infix(x,\snoc(b,y)) = \bor(\suffix(x,\snoc(b,y)),\infix(x,y))$.
</p></div>

<div class="proof"><p>
1. Note that, for all $x,u,v \in \lists{A}$, we have
$$\begin{eqnarray*}
 &   & \rev(\cat(u,\cat(x,v))) \\
 & = & \cat(\rev(\cat(x,v)),\rev(u)) \\
 & = & \cat(\cat(\rev(v),\rev(x)),\rev(u)) \\
 & = & \cat(\rev(v),\cat(\rev(x),\rev(u))).
\end{eqnarray*}$$
In particular, $$y = \cat(u,\cat(x,v))$$ for some $u$ and $v$ if and only if $$\rev(y) = \cat(h,\cat(\rev(x),k))$$ for some $h$ and $k$. So $\infix(x,y) = \btrue$ if and only if $\infix(\rev(x),\rev(y)) = \btrue$.
2. We consider two cases for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \infix(\snoc(a,x),\nil) \\
 & = & \infix(\snoc(a,\nil),\nil) \\
 & = & \infix(\cons(a,\nil),\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed. If $x = \cons(b,u)$, we have
$$\begin{eqnarray*}
 &   & \infix(\snoc(a,x),\nil) \\
 & = & \infix(\snoc(a,\cons(b,u)),\nil) \\
 & = & \infix(\cons(b,\snoc(a,u)),\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \infix(x,\snoc(b,y)) \\
 & = & \infix(\rev(x),\rev(\snoc(b,y))) \\
 & = & \infix(\rev(x),\cons(b,\rev(y))) \\
 & = & \bor(\prefix(\rev(x),\cons(b,\rev(y))),\infix(\rev(x),\rev(y))) \\
 & = & \bor(\prefix(\rev(x),\rev(\snoc(b,y))),\infix(x,y)) \\
 & = & \bor(\suffix(x,\snoc(b,y)),\infix(x,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\infix$ is a partial order:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,z \in \lists{A}$.

1. If $\infix(x,y) = \btrue$ and $\infix(y,x) = \btrue$, then $x = y$.
2. If $\infix(x,y) = \btrue$ and $\infix(y,z) = \btrue$, then $\infix(x,z) = \btrue$.
</p></div>

<div class="proof"><p>
1. Suppose $\infix(x,y) = \btrue$; then we have $u$ and $v$ such that $$y = \cat(u,\cat(x,v)).$$ Similarly, if $\infix(y,x) = \btrue$ we have $h$ and $k$ such that $$x = \cat(h,\cat(y,k)).$$ Now
$$\begin{eqnarray*}
 &   & x \\
 & = & \cat(h,\cat(y,k)) \\
 & = & \cat(h,\cat(\cat(u,\cat(x,v)),k)) \\
 & = & \cat(\cat(h,u),\cat(\cat(x,v),k)) \\
 & = & \cat(\cat(h,u),\cat(x,\cat(v,k))),
\end{eqnarray*}$$
so that $\cat(h,u) = \nil$ and $\cat(v,k) = \nil$. Thus $h = k = \nil$, and we have
$$\begin{eqnarray*}
 &   & x \\
 & = & \cat(h,\cat(y,k)) \\
 & = & \cat(\nil,\cat(y,\nil)) \\
 & = & \cat(\nil,y) \\
 & = & y
\end{eqnarray*}$$
as claimed.
2. If $\infix(x,y) = \btrue$, we have $$y = \cat(u,\cat(x,v))$ for some $u$ and $v$, and if $\infix(y,z) = \btrue$ we have $$z = \cat(h,cat(y,k))$ for some $h$ and $k$. Now
$$\begin{eqnarray*}
 &   & z \\
 & = & \cat(h,\cat(y,k)) \\
 & = & \cat(h,\cat(\cat(u,\cat(x,v)),k)) \\
 & = & \cat(\cat(h,u),\cat(\cat(x,v),k)) \\
 & = & \cat(\cat(h,u),\cat(x,\cat(v,k)))
\end{eqnarray*}$$
so that $\infix(x,z) = \btrue$ as claimed.
</p></div>
</div>

And infixes are also sublists:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y \in \lists{A}$.

1. If $\infix(x,y) = \btrue$, then $\sublist(x,y) = \btrue$.
2. If $\prefix(x,y) = \btrue$, then $\sublist(x,y) = \btrue$.
3. If $\suffix(x,y) = \btrue$, then $\sublist(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $y$. For the base case $y = \nil$, note that if $$\btrue = \infix(x,y) = \infix(x,\nil),$$ we have $x = \nil$. Then $$\sublist(x,y) = \sublist(\nil,y) = \btrue$$ as needed. For the inductive step, suppose the implication holds for all $x$ for some $y$, and let $a \in A$. Suppose further that $\infix(x,\cons(a,y)) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\infix(x,y)).
\end{eqnarray*}$$
We consider two possibilities. If $\prefix(x,\cons(a,y)) = \btrue$, we consider two possibilities for $x$. If $x = \nil$, we have $$\sublist(x,\cons(a,y)) = \sublist(\nil,\cons(a,y)) = \btrue$$ as needed. Suppose then that $x = \cons(b,u)$; since $\prefix(x,\cons(a,y)) = \btrue$, we have $b = a$ and $\prefix(u,y) = \btrue$. Now $\infix(u,y)$, and by the induction hypothesis $\sublist(u,y) = \btrue$, so that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(u,y) \\
 & = & \sublist(\cons(a,u),\cons(a,y)) \\
 & = & \sublist(\cons(b,u),\cons(a,y)) \\
 & = & \sublist(x,\cons(a,y))
\end{eqnarray*}$$
as needed. Now suppose $\infix(x,y) = \btrue$. By the induction hypothesis, we have $\sublist(x,y) = \btrue$, so that $\sublist(x,\cons(b,y)) = \btrue$ as needed.
2. If $\prefix(x,y) = \btrue$, then $\infix(x,y) = \btrue$.
3. If $\suffix(x,y) = \btrue$, then $\infix(x,y) = \btrue$.
</p></div>
</div>


Testing
-------

Here are our property tests for $\infix$:

> _test_infix_nil_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_infix_nil_left _ =
>   testName "infix(nil,x) == true" $
>   \x -> eq (isInfix nil x) True
> 
> 
> _test_infix_nil_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_infix_nil_right _ =
>   testName "infix(cons(a,x),nil) == false" $
>   \a x -> eq (isInfix (cons a x) nil) False
> 
> 
> _test_infix_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_cat_right _ =
>   testName "infix(x,cat(x,y)) = true" $
>   \x y -> isInfix x (cat x y)
> 
> 
> _test_infix_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_cat_left _ =
>   testName "infix(x,cat(y,x)) = true" $
>   \x y -> isInfix x (cat y x)
> 
> 
> _test_infix_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> a -> t a -> Bool)
> _test_infix_cons _ =
>   testName "infix(x,cons(b,y)) == or(prefix(x,cons(b,y)),infix(x,y))" $
>   \x b y -> eq
>     (isInfix x (cons b y))
>     (or (prefix x (cons b y)) (isInfix x y))
> 
> 
> _test_infix_snoc_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_infix_snoc_nil _ =
>   testName "infix(snoc(a,x),nil) == false" $
>   \a x -> eq (isInfix (snoc a x) nil) False
> 
> 
> _test_infix_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> a -> t a -> Bool)
> _test_infix_snoc _ =
>   testName "infix(x,snoc(b,y)) == or(suffix(x,snoc(b,y)),infix(x,y))" $
>   \x b y -> eq
>     (isInfix x (snoc b y))
>     (or (suffix x (snoc b y)) (isInfix x y))
> 
> 
> _test_infix_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_rev _ =
>   testName "infix(rev(x),rev(y)) == infix(x,y)" $
>   \x y -> eq (isInfix (rev x) (rev y)) (isInfix x y)
> 
> 
> _test_infix_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_cat _ =
>   testName "infix(x,cat(u,cat(x,v)))" $
>   \x u v -> isInfix x (cat u (cat x v))
> 
> 
> _test_infix_reflexive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_infix_reflexive _ =
>   testName "infix(x,x) == true" $
>   \x -> eq (isInfix x x) True
> 
> 
> _test_infix_symmetric :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_symmetric _ =
>   testName "infix(x,y) & infix(y,x) ==> eq(x,y)" $
>   \x y -> if and (isInfix x y) (isInfix y x)
>     then eq x y
>     else True
> 
> 
> _test_infix_transitive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_transitive _ =
>   testName "infix(x,y) & infix(y,z) ==> sublist(x,z)" $
>   \x y z -> if and (isInfix x y) (isInfix y z)
>     then isInfix x z
>     else True
> 
> 
> _test_infix_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_prefix _ =
>   testName "prefix(x,y) ==> infix(x,y)" $
>   \x y -> if prefix x y
>     then isInfix x y
>     else True
> 
> 
> _test_infix_suffix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_suffix _ =
>   testName "suffix(x,y) ==> infix(x,y)" $
>   \x y -> if suffix x y
>     then isInfix x y
>     else True
> 
> 
> _test_infix_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_sublist _ =
>   testName "infix(x,y) ==> sublist(x,y)" $
>   \x y -> if isInfix x y
>     then sublist x y
>     else True

Suite:

> _test_isInfix ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_isInfix t maxSize numCases = do
>   testLabel ("infix: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_infix_nil_left t)
>   runTest args (_test_infix_nil_right t)
>   runTest args (_test_infix_cons t)
>   runTest args (_test_infix_cat_left t)
>   runTest args (_test_infix_cat_right t)
>   runTest args (_test_infix_snoc_nil t)
>   runTest args (_test_infix_snoc t)
>   runTest args (_test_infix_rev t)
>   runTest args (_test_infix_cat t)
>   runTest args (_test_infix_reflexive t)
>   runTest args (_test_infix_symmetric t)
>   runTest args (_test_infix_transitive t)
>   runTest args (_test_infix_prefix t)
>   runTest args (_test_infix_suffix t)
>   runTest args (_test_infix_sublist t)

Main:

> main_isInfix :: IO ()
> main_isInfix = do
>   _test_isInfix (nil :: ConsList Bool)  30 200
>   _test_isInfix (nil :: ConsList Unary) 30 200
