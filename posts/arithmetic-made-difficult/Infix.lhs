---
title: Infix
author: nbloomf
date: 2017-05-24
tags: arithmetic-made-difficult, literate-haskell
---

> module Infix
>   ( isInfix, _test_isInfix, main_isInfix
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
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Sublist
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll nail down ``infix``, a variant on ``sublist``.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\infix : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\infix(x,y) = \any(\prefix(x,-),\tails(y)).$$

In Haskell:

> isInfix :: (List t, Equal a) => t a -> t a -> Bool
> isInfix x y = any (prefix x) (tails y)

</p></div>
</div>

(``infix`` is a reserved word in Haskell, so we'll call this function ``isInfix``.)

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
We have two possibilities. If $\prefix(x,\cons(a,y)) = \btrue$, then $\cons(a,y) = \cat(x,z)$ for some $z$; then $\cons(a,y) = \cat(\nil,\cat(x,z))$ as needed. Suppose instead that $\infix(x,y) = \btrue$. By the inductive hypothesis we have $y = \cat(u,\cat(x,v))$ for some $u$ and $v$, so that
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

1. $\infix(\snoc(a,x),\nil) = \bfalse$.
2. $\infix(x,\snoc(b,y)) = \bor(\suffix(x,\snoc(b,y)),\infix(x,y))$.
3. $\infix(\rev(x),\rev(y)) = \infix(x,y)$.
</p></div>

<div class="proof"><p>
1. We consider two cases for $x$. If $x = \nil$, we have
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
2. We begin by proving the following statement: for all $x$, $y$, and $b$, we have $$\any(\prefix(x,\snoc(b,-)),\tails(y)) = \bor(\suffix(x,\snoc(b,y)),\infix(x,y)).$$ We proceed by list induction on $y$. For the base case $y = \nil$, we have
(@@@)
For the inductive step, suppose the equality holds for all $x$ for some $y$ and let $c \in A$. Now
$$\begin{eqnarray*}
 &   & \bor(\suffix(x,\snoc(b,\cons(c,y))),\infix(x,\cons(c,y))) \\
 & = & \bor(\suffix(x,\snoc(b,\cons(c,y))),\bor(\prefix(x,\cons(c,y)),\infix(x,y))) \\
\end{eqnarray*}$$

Now for the main result: we consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \infix(x,\snoc(b,y)) \\
 & = & \infix(\nil,\snoc(b,y)) \\
 & = & \btrue \\
 & = & \bor(\btrue,\btrue) \\
 & = & \bor(\suffix(\nil,\snoc(b,y)),\infix(\nil,y)) \\
 & = & \bor(\suffix(x,\snoc(b,y)),\infix(x,y))
\end{eqnarray*}$$
as claimed. Suppose now that $x = \cons(a,u)$. Now we have
$$\begin{eqnarray*}
 &   & \infix(x,\snoc(b,y)) \\
 & = & \any(\prefix(x,-),\tails(\snoc(b,y))) \\
 & = & \any(\prefix(x,-),\cons(\nil,\map(\snoc(b,-))(\tails(y)))) \\
 & = & \bor(\prefix(x,\nil),\any(\prefix(x,-),\map(\snoc(b,-))(\tails(y)))) \\
 & = & \bor(\prefix(\cons(a,u),\nil),\any(\prefix(x,-),\map(\snoc(b,-))(\tails(y)))) \\
 & = & \bor(\bfalse,\any(\prefix(x,-),\map(\snoc(b,-))(\tails(y)))) \\
 & = & \any(\prefix(x,-),\map(\snoc(b,-))(\tails(y))) \\
 & = & \any(\prefix(x,-) \circ \snoc(b,-), \tails(y)) \\
 & = & \any(\prefix(x,\snoc(b,-)),\tails(y)) \\
 & = & (@@@) \\
 & = & \bor(\suffix(x,\snoc(b,y)),\infix(x,y))
\end{eqnarray*}$$
3. (@@@)
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
1. (@@@)
2. (@@@)
</p></div>
</div>

And infixes are also sublists:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y \in \lists{A}$. If $\infix(x,y) = \btrue$, then $\sublist(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Testing
-------

Here are our property tests for $\infix$:

> -- infix(nil,x) == true
> _test_infix_nil_left :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_infix_nil_left _ x =
>    (isInfix nil x) ==== True
> 
> 
> -- infix(cons(a,x),nil) == false
> _test_infix_nil_right :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_infix_nil_right _ a x =
>    (isInfix (cons a x) nil) ==== False
> 
> 
> -- infix(x,cat(x,y)) = true
> _test_infix_cat_right :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_cat_right _ x y =
>    isInfix x (cat x y)
> 
> 
> -- infix(x,cat(y,x)) = true
> _test_infix_cat_left :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_cat_left _ x y =
>    isInfix x (cat y x)
> 
> 
> -- infix(x,cons(b,y)) == or(prefix(x,cons(b,y)),infix(x,y))
> _test_infix_cons :: (List t, Equal a)
>   => t a -> ListOf t a -> a -> ListOf t a -> Bool
> _test_infix_cons _ x b y =
>    eq
>      (isInfix x (cons b y))
>      (or (prefix x (cons b y)) (isInfix x y))
> 
> 
> -- infix(snoc(a,x),nil) == false
> _test_infix_snoc_nil :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_infix_snoc_nil _ a x =
>    (isInfix (snoc a x) nil) ==== False
> 
> 
> -- infix(x,snoc(b,y)) == or(suffix(x,snoc(b,y)),infix(x,y))
> _test_infix_snoc :: (List t, Equal a)
>   => t a -> ListOf t a -> a -> ListOf t a -> Bool
> _test_infix_snoc _ x b y =
>    eq
>      (isInfix x (snoc b y))
>      (or (suffix x (snoc b y)) (isInfix x y))
> 
> 
> -- infix(rev(x),rev(y)) == infix(x,y)
> _test_infix_rev :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_rev _ x y =
>    (isInfix (rev x) (rev y)) ==== (isInfix x y)
> 
> 
> -- infix(x,cat(u,cat(x,v)))
> _test_infix_cat :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_cat _ x u v =
>    isInfix x (cat u (cat x v))
> 
> 
> -- infix(x,x) == true
> _test_infix_reflexive :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_infix_reflexive _ x =
>    (isInfix x x) ==== True
> 
> 
> -- infix(x,y) & infix(y,x) ==> eq(x,y)
> _test_infix_symmetric :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_symmetric _ x y =
>    if (isInfix x y) &&& (isInfix y x)
>      then x ==== y
>      else True
> 
> 
> -- infix(x,y) & infix(y,z) ==> sublist(x,z)
> _test_infix_transitive :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_transitive _ x y z =
>    if (isInfix x y) &&& (isInfix y z)
>      then isInfix x z
>      else True
> 
> 
> -- prefix(x,y) ==> infix(x,y)
> _test_infix_prefix :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_prefix _ x y =
>    if prefix x y
>      then isInfix x y
>      else True
> 
> 
> -- suffix(x,y) ==> infix(x,y)
> _test_infix_suffix :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_suffix _ x y =
>    if suffix x y
>      then isInfix x y
>      else True
> 
> 
> -- infix(x,y) ==> sublist(x,y)
> _test_infix_sublist :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_infix_sublist _ x y =
>    if isInfix x y
>      then sublist x y
>      else True

And the suite:

> -- run all tests for infix
> _test_isInfix ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
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

And ``main``:

> main_isInfix :: IO ()
> main_isInfix = do
>   _test_isInfix (nil :: ConsList Bool)  30 200
>   _test_isInfix (nil :: ConsList Unary) 30 200
