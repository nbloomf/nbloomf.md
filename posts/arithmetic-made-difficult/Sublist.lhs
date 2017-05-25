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
Let $A$ be a set with $a \in A$ and $x,y \in \lists{A}$. Then we have the following.

1. $\sublist(x,y) = \sublist(\cons(a,x),\cons(a,y))$.
2. If $\sublist(\cons(a,x),y) = \btrue$, then $\sublist(x,y) = \btrue$.
3. If $\sublist(x,y) = \btrue$, then $\sublist(x,\cons(b,y)) = \btrue$.
4. $\sublist(x,y) = \sublist(\snoc(a,x),\snoc(a,y))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \sublist(\cons(a,x),\cons(a,y)) \\
 & = & \bif{\beq(a,a)}{\sublist(x,y)}{\sublist(\cons(a,x),y)} \\
 & = & \sublist(x,y)
\end{eqnarray*}$$
as claimed.
2. (@@@)
3. (@@@)
4. (@@@)
</p></div>
</div>

Now $\sublist$ interacts with $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x,y \in \lists{A}$. If $\sublist(x,y)$, then $\leq(\length(x),\length(y))$.
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
 &   & \leq(\length(x),\length(y)) \\
 & = & \leq(\zero,\zero) \\
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
 &   & \leq(\length(x),\length(\cons(b,y))) \\
 & = & \leq(\length(\nil),\length(\cons(b,y))) \\
 & = & \leq(\zero,\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose then that $x = \cons(a,u)$, and suppose further that $\sublist(x,\cons(b,y)) = \btrue$. We have two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(x,\cons(b,y)) \\
 & = & \sublist(\cons(a,u),\cons(b,y)) \\
 & = & \sublist(u,y).
\end{eqnarray*}$$
By the induction hypothesis, we have
$$\begin{eqnarray*
 &   & \btrue \\
 & = & \leq(\length(u),\length(y)) \\
 & = & \leq(\next(\length(u)),\next(\length(y))) \\
 & = & \leq(\length(\cons(a,u)),\length(\cons(b,y))) \\
 & = & \leq(\length(x),\length(\cons(b,y)))
</p></div>
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
 & = & \leq(\length(\cons(a,u)),\length(y)) \\
 & = & \leq(\length(x),\length(y)) \\
 & = & \leq(\length(x),\next(\length(y))) \\
 & = & \leq(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed.
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
 & = & \leq(\lenth(\cons(a,x)),\length(y)) \\
 & = & \leq(\next(\length(x)),\length(y)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \leq(\length(y),\length(x));
\end{eqnarray*}$$
by transitivity, we thus also have $$\leq(\next(\length(x)),\length(x)),$$ a contradiction. So in fact $a = b$. Thus we have
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


<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,u,v \in \lists{A}$.

1. If $\sublist(x,y)$, then $\sublist(\cat(u,x),\cat(u,y))$.
2. If $\sublist(x,y)$, then $\sublist(\cat(x,u),\cat(y,u))$.
3. If $\sublist(x,u)$ and $\sublist(y,v)$, then $\sublist(\cat(x,u),\cat(y,v))$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
3. (@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $\sublist(x,y)$ if and only if $\sublist(\rev(x),\rev(y))$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set, let $x,y \in \lists{A}$, and let $p : A \rightarrow \bool$. If $\sublist(x,y)$, then we have the following.

1. If $\all(p,y)$ then $\all(p,x)$.
2. If $\any(p,x)$ then $\any(p,y)$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

Now for $\infix$.

<div class="result">
<div class="defn"><p>
(@@@)

In Haskell:

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>


Testing
-------

Here are our property tests for $\sublist$:

> -- sublist'(x,y) == sublist(x,y)
> _test_sublist_alt :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_alt _ x y =
>    (sublist' x y) ==== (sublist x y)
> 
> 
> -- sublist(x,x) == true
> _test_sublist_reflexive :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_sublist_reflexive _ x =
>    (sublist x x) ==== True
> 
> 
> -- sublist(x,y) & sublist(y,x) ==> eq(x,y)
> _test_sublist_antisymmetric :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_antisymmetric _ x y =
>    ((sublist x y) &&& (sublist y x)) ==== (eq x y)
> 
> 
> -- sublist(x,y) & sublist(y,z) ==> sublist(x,z)
> _test_sublist_transitive :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_transitive _ x y z =
>    if (sublist x y) &&& (sublist y z)
>      then sublist x z
>      else True
> 
> 
> -- sublist(x,y) == sublist(rev(x),rev(y))
> _test_sublist_rev :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_rev _ x y =
>    (sublist x y) ==== (sublist (rev x) (rev y))
> 
> 
> -- sublist(x,y) ==> sublist(cat(u,x),cat(u,y))
> _test_sublist_cat_left :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_cat_left _ x y u =
>    if sublist x y
>      then sublist (cat u x) (cat u y)
>      else True
> 
> 
> -- sublist(x,y) ==> sublist(cat(x,u),cat(y,u))
> _test_sublist_cat_right :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_cat_right _ x y u =
>    if sublist x y
>      then sublist (cat x u) (cat y u)
>      else True
> 
> 
> -- sublist(x,y) & sublist(u,v) ==> sublist(cat(x,u),cat(y,v))
> _test_sublist_cat :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_sublist_cat _ x y u v =
>    if (sublist x y) &&& (sublist u v)
>      then sublist (cat x u) (cat y v)
>      else True

And the suite:

> -- run all tests for sublist and isInfix
> _test_sublist ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_sublist t maxSize numCases = do
>   testLabel ("sublist & isInfix: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_sublist_alt t)
>   runTest args (_test_sublist_reflexive t)
>   runTest args (_test_sublist_antisymmetric t)
>   runTest args (_test_sublist_transitive t)
>   runTest args (_test_sublist_rev t)
>   runTest args (_test_sublist_cat_left t)
>   runTest args (_test_sublist_cat_right t)
>   runTest args (_test_sublist_cat t)

And ``main``:

> main_sublist :: IO ()
> main_sublist = do
>   _test_sublist (nil :: ConsList Bool)  30 200
>   _test_sublist (nil :: ConsList Unary) 30 200
