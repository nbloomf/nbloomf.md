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
> import BailoutFold
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

Today we'll nail down $\infix$, a variant on $\sublist$.

<div class="result">
<div class="dfn"><p>
Let $A$ be a set. Define $\beta : A \times \lists{A} \times \lists{A} \rightarrow \bool$ by $$\beta(a,x,y) = \prefix(y,\cons(a,x)),$$ $\psi : A \times \lists{A} \times \lists{A} \rightarrow \bool$ by $$\beta(a,x,y) = \btrue,$$ and $\omega : A \times \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\omega(a,x,y) = y.$$ Then define $\infix : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\infix(x,y) = \bfoldr{\isnil}{\beta}{\psi}{\omega}(y,x).$$

In Haskell:

> isInfix :: (List t, Equal a) => t a -> t a -> Bool
> isInfix x y = bfoldr isNil beta psi omega y x
>   where
>     beta a x y = prefix y (cons a x)
>     psi _ _ _ = True
>     omega _ _ y = y

</p></div>
</div>

(``infix`` is a reserved word in Haskell, so we'll call this function ``isInfix``.)

Since $\infix$ is defined in terms of bailout fold, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. $\infix$ is the unique map $f : \lists{A} \times \lists{A} \rightarrow \bool$ satisfying the following equations for all $b \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(x,\nil) = \isnil(x) \\
 f(x,\cons(b,y)) = \bif{\prefix(x,\cons(b,y))}{\btrue}{f(x,y)}
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_infix_list_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_infix_list_nil _ =
>   testName "infix(x,nil) == isNil(x)" $
>   \x -> eq (isInfix x nil) (isNil x)
> 
> 
> _test_infix_list_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> a -> t a -> Bool)
> _test_infix_list_cons _ =
>   testName "infix(x,cons(b,y)) == if(prefix(x,cons(b,y)),true,infix(x,y))" $
>   \x b y -> eq
>     (isInfix x (cons b y))
>     (if prefix x (cons b y) then True else isInfix x y)

</p></div>
</div>

$\infix$ is an $\bor$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\infix(x,y) = \bor(\prefix(x,y),\infix(x,\tail(y))).$$
</p></div>

<div class="proof"><p>
We consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \infix(x,\nil) \\
 & = & \isnil(x) \\
 & = & \bor(\isnil(x),\isnil(x)) \\
 & = & \bor(\prefix(x,\nil),\infix(x,\nil)) \\
 & = & \bor(\prefix(x,\nil),\infix(x,\tail(\nil)))
\end{eqnarray*}$$
as needed. If $y = \cons(b,u)$, we have
$$\begin{eqnarray*}
 &   & \infix(x,\cons(b,u)) \\
 & = & \bif{\prefix(x,\cons(b,u))}{\btrue}{\infix(x,u)} \\
 & = & \bor(\prefix(x,\cons(b,u)),\infix(x,u)) \\
 & = & \bor(\prefix(x,y),\infix(x,\tail(y)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_infix_prefix_or :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_prefix_or _ =
>   testName "infix(x,y) == or(prefix(x,y),infix(x,tail(y)))" $
>   \x y -> eq (isInfix x y) (or (prefix x y) (isInfix x (tail y)))

</p></div>
</div>

$\infix$ is reflexive.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $x \in \lists{A}$, then $\infix(x,x) = \btrue$.
</p></div>

<div class="proof"><p>
We consider two cases for $x$. If $x = \nil$, we have $$\infix(x,x) = \infix(\nil,\nil) = \btrue$$ as claimed. If $x = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \infix(x,x) \\
 & = & \infix(x,\cons(a,u)) \\
 & = & \bif{\prefix(x,\cons(a,u))}{\btrue}{\infix(x,u)} \\
 & = & \bif{\prefix(x,x)}{\btrue}{\infix(x,u)} \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_infix_reflexive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_infix_reflexive _ =
>   testName "infix(x,x) == true" $
>   \x -> eq (isInfix x x) True

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
 & = & \infix(x,\cons(b,\cat(y,x))) \\
 & = & \bor(\prefix(x,\cons(b,\cat(y,x))),\infix(x,\cat(y,x))) \\
 & = & \bor(\prefix(x,\cons(b,\cat(y,x))),\btrue) \\
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

<div class="test"><p>

> _test_infix_cat_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_cat_right _ =
>   testName "infix(x,cat(x,y)) == true" $
>   \x y -> isInfix x (cat x y)
> 
> 
> _test_infix_cat_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_cat_left _ =
>   testName "infix(x,cat(y,x)) == true" $
>   \x y -> isInfix x (cat y x)

</p></div>
</div>

Prefixes and suffixes are also infixes.

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

<div class="test"><p>

> _test_infix_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_prefix _ =
>   testName "if prefix(x,y) then infix(x,y)" $
>   \x y -> if prefix x y then isInfix x y else True
> 
> 
> _test_infix_suffix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_suffix _ =
>   testName "if suffix(x,y) then infix(x,y)" $
>   \x y -> if suffix x y then isInfix x y else True

</p></div>
</div>

$\infix$ interacts conditionally with $\cons$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. If $\infix(x,y) = \btrue$, then $\infix(x,\cons(a,y)) = \btrue$.
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\infix(x,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_infix_cond_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> a -> Bool)
> _test_infix_cond_cons _ =
>   testName "if infix(x,y) then infix(x,cons(a,y))" $
>   \x y a -> if isInfix x y then isInfix x (cons a y) else True

</p></div>
</div>

$\infix$ interacts conditionally with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. If $\infix(x,y) = \btrue$, then $\infix(x,\snoc(a,y)) = \btrue$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, note that we must have $x = \nil$. Now $$\infix(x,\snoc(a,y)) = \infix(\nil,\snoc(a,y)) = \btrue$$ as needed. For the inductive step, suppose the implication holds for some $y$ and let $b \in A$. Suppose further that $\infix(x,\cons(b,y)) = \btrue$. Now
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

<div class="test"><p>

> _test_infix_cond_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> a -> Bool)
> _test_infix_cond_snoc _ =
>   testName "if infix(x,y) then infix(x,snoc(a,y))" $
>   \x y a -> if isInfix x y then isInfix x (snoc a y) else True

</p></div>
</div>

$\infix$ is right-compatible with $\cat$ (from both sides).

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

<div class="test"><p>

> _test_infix_cat_right_compatible_right :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_cat_right_compatible_right _ =
>   testName "if infix(x,y) then infix(x,cat(y,z))" $
>   \x y z -> if isInfix x y then isInfix x (cat y z) else True
> 
> 
> _test_infix_cat_right_compatible_left :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_cat_right_compatible_left _ =
>   testName "if infix(x,y) then infix(x,cat(z,y))" $
>   \x y z -> if isInfix x y then isInfix x (cat z y) else True

</p></div>
</div>

$\infix$ perfectly detects two-sided $\cat$-factorizations.

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

<div class="test"><p>

> _test_infix_cat_factor :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_cat_factor _ =
>   testName "infix(x,cat(u,cat(x,v)))" $
>   \x u v -> isInfix x (cat u (cat x v))

</p></div>
</div>

$\infix$ interacts with $\rev$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $x \in \lists{A}$, we have $\infix(\rev(x),\rev(y)) = \infix(x,y)$.
</p></div>

<div class="proof"><p>
Note that, for all $x,u,v \in \lists{A}$, we have
$$\begin{eqnarray*}
 &   & \rev(\cat(u,\cat(x,v))) \\
 & = & \cat(\rev(\cat(x,v)),\rev(u)) \\
 & = & \cat(\cat(\rev(v),\rev(x)),\rev(u)) \\
 & = & \cat(\rev(v),\cat(\rev(x),\rev(u))).
\end{eqnarray*}$$
In particular, $$y = \cat(u,\cat(x,v))$$ for some $u$ and $v$ if and only if $$\rev(y) = \cat(h,\cat(\rev(x),k))$$ for some $h$ and $k$. So $\infix(x,y) = \btrue$ if and only if $\infix(\rev(x),\rev(y)) = \btrue$.
</p></div>

<div class="test"><p>

> _test_infix_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_rev _ =
>   testName "infix(rev(x),rev(y)) == infix(x,y)" $
>   \x y -> eq (isInfix (rev x) (rev y)) (isInfix x y)

</p></div>
</div>

$\snoc(a,x)$ is not an infix of $\nil$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have $$\infix(\snoc(a,x),\nil) = \bfalse.$$
</p></div>

<div class="proof"><p>
$$\begin{eqnarray*}
 &   & \infix(\snoc(a,x),\nil) \\
 & = & \isnil(\snoc(a,x)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_infix_snoc_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_infix_snoc_nil _ =
>   testName "infix(snoc(a,x),nil) == false" $
>   \a x -> eq (isInfix (snoc a x) nil) False

</p></div>
</div>

$\infix$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ and $b \in A$, we have $$\infix(x,\snoc(b,y)) = \bor(\suffix(x,\snoc(b,y)),\infix(x,y)).$$
</p></div>

<div class="proof"><p>
Note that
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

<div class="test"><p>

> _test_infix_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> a -> t a -> Bool)
> _test_infix_snoc _ =
>   testName "infix(x,snoc(b,y)) == or(suffix(x,snoc(b,y)),infix(x,y))" $
>   \x b y -> eq
>     (isInfix x (snoc b y))
>     (or (suffix x (snoc b y)) (isInfix x y))

</p></div>
</div>

$\infix$ is antisymmetric.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. If $\infix(x,y) = \btrue$ and $\infix(y,x) = \btrue$, then $x = y$.
</p></div>

<div class="proof"><p>
Suppose $\infix(x,y) = \btrue$; then we have $u$ and $v$ such that $$y = \cat(u,\cat(x,v)).$$ Similarly, if $\infix(y,x) = \btrue$ we have $h$ and $k$ such that $$x = \cat(h,\cat(y,k)).$$ Now
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
</p></div>

<div class="test"><p>

> _test_infix_antisymmetric :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_antisymmetric _ =
>   testName "infix(x,y) & infix(y,x) ==> eq(x,y)" $
>   \x y -> if and (isInfix x y) (isInfix y x)
>     then eq x y
>     else True

</p></div>
</div>

$\infix$ is transitive.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y,z \in \lists{A}$. If $\infix(x,y) = \btrue$ and $\infix(y,z) = \btrue$, then $\infix(x,z) = \btrue$.
</p></div>

<div class="proof"><p>
If $\infix(x,y) = \btrue$, we have $$y = \cat(u,\cat(x,v))$ for some $u$ and $v$, and if $\infix(y,z) = \btrue$ we have $$z = \cat(h,cat(y,k))$ for some $h$ and $k$. Now
$$\begin{eqnarray*}
 &   & z \\
 & = & \cat(h,\cat(y,k)) \\
 & = & \cat(h,\cat(\cat(u,\cat(x,v)),k)) \\
 & = & \cat(\cat(h,u),\cat(\cat(x,v),k)) \\
 & = & \cat(\cat(h,u),\cat(x,\cat(v,k)))
\end{eqnarray*}$$
so that $\infix(x,z) = \btrue$ as claimed.
</p></div>

<div class="test"><p>

> _test_infix_transitive :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_infix_transitive _ =
>   testName "infix(x,y) & infix(y,z) ==> sublist(x,z)" $
>   \x y z -> if and (isInfix x y) (isInfix y z)
>     then isInfix x z
>     else True

</p></div>
</div>

Infixes are also sublists:

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

<div class="test"><p>

> _test_infix_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_sublist _ =
>   testName "if infix(x,y) then sublist(x,y)" $
>   \x y -> if isInfix x y then sublist x y else True
> 
> 
> _test_prefix_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_prefix_sublist _ =
>   testName "if prefix(x,y) then sublist(x,y)" $
>   \x y -> if prefix x y then sublist x y else True
> 
> 
> _test_suffix_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_suffix_sublist _ =
>   testName "if suffix(x,y) then sublist(x,y)" $
>   \x y -> if suffix x y then sublist x y else True

</p></div>
</div>

$\infix$ is an $\any$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\infix(x,y) = \any(\prefix(x,-))(\tails(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \any(\prefix(x,-))(\tails(\nil)) \\
 & = & \any(\prefix(x,-))(\cons(\nil,\nil)) \\
 & = & \bor(\prefix(x,\nil),\any(\prefix(x,-))(\nil)) \\
 & = & \bor(\prefix(x,\nil),\btrue) \\
 & = & \prefix(x,\nil) \\
 & = & \isnil(x) \\
 & = & \infix(x,y)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $y$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \infix(x,\cons(a,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\infix(x,y)) \\
 & = & \bor(\prefix(x,\cons(a,y)),\any(\prefix(x,))(\tails(y))) \\
 & = & \any(\prefix(x,-))(\cons(\cons(a,y),\tails(y))) \\
 & = & \any(\prefix(x,-))(\tails(\cons(a,y)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_infix_any :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_infix_any _ =
>   testName "infix(x,y) == any(prefix(x,-))(tails(y))" $
>   \x y -> eq (isInfix x y) (any (prefix x) (tails y))

</p></div>
</div>


Testing
-------

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
>   runTest args (_test_infix_list_nil t)
>   runTest args (_test_infix_list_cons t)
>   runTest args (_test_infix_prefix_or t)
>   runTest args (_test_infix_reflexive t)
>   runTest args (_test_infix_cat_right t)
>   runTest args (_test_infix_cat_left t)
>   runTest args (_test_infix_prefix t)
>   runTest args (_test_infix_suffix t)
>   runTest args (_test_infix_cond_cons t)
>   runTest args (_test_infix_cond_snoc t)
>   runTest args (_test_infix_cat_right_compatible_right t)
>   runTest args (_test_infix_cat_right_compatible_left t)
>   runTest args (_test_infix_cat_factor t)
>   runTest args (_test_infix_rev t)
>   runTest args (_test_infix_snoc_nil t)
>   runTest args (_test_infix_snoc t)
>   runTest args (_test_infix_antisymmetric t)
>   runTest args (_test_infix_transitive t)
>   runTest args (_test_infix_sublist t)
>   runTest args (_test_prefix_sublist t)
>   runTest args (_test_suffix_sublist t)
>   runTest args (_test_infix_any t)

Main:

> main_isInfix :: IO ()
> main_isInfix = do
>   _test_isInfix (nil :: ConsList Bool)  30 1000
>   _test_isInfix (nil :: ConsList Unary) 30 1000
