---
title: Elt
author: nbloomf
date: 2017-05-20
tags: arithmetic-made-difficult, literate-haskell
slug: elt
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Elt
>   ( elt, _test_elt, main_elt
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import LessThanOrEqualTo
> import Lists
> import Snoc
> import Reverse
> import Length
> import Map
> import Range
> import Cat
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter

Today we'll define a boolean function, $\elt$, which detects whether or not a given $a$ is an item in a list. As usual we want to define $\elt$ as a fold: should we use a right fold or a left fold? Recall that the tradeoff between the two is that foldl is tail recursive, but foldr does not necessarily have to process the entire list. In this case, $\elt(a)(x)$ should be able to return early once it sees an $a$. So lets say $$\elt(a)(x) = \foldr{\varepsilon}{\varphi}(x).$$ Now what should $\varepsilon$ and $\varphi$ be? Well, we want
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \elt(a)(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(x) \\
 & = & \varepsilon,
\end{eqnarray*}$$
and if $a = b$ we want
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \elt(a)(\cons(b,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(b,x)) \\
 & = & \varphi(b,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(b,\elt(a)(x))
\end{eqnarray*}$$
while if $a \neq b$ we want
$$\begin{eqnarray*}
 &   & \elt(a)(x) \\
 & = & \elt(a)(\cons(b,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(b,x)) \\
 & = & \varphi(b,\foldr{\varepsilon}{\varphi}(x)) \\
 & = & \varphi(b,\elt(a)(x)).
\end{eqnarray*}$$
With this in mind we define $\elt$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set and let $a \in A$. Define $\varphi : A \rightarrow \bool \rightarrow \bool$ by $$\varphi(b,p) = \bif{\beq(a,b)}{\btrue}{p}.$$ Now define $\elt : A \rightarrow \bool^{\lists{A}}$ by $$\elt(a)(x) = \foldr{\bfalse}{\varphi}(x).$$

In Haskell:

> elt :: (List t, Equal a) => a -> t a -> Bool
> elt a = foldr False phi
>   where
>     phi b p = if eq a b then True else p

</p></div>
</div>

Since $\elt$ is defined as a $\foldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set with $a \in A$. $\elt$ is the unique map $f : \lists{A} \rightarrow \bool$ satisfying the following equations for all $b \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \bfalse \\
 f(\cons(b,x)) = \bif{\beq(a,b)}{\btrue}{f(x)}
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_elt_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> Bool)
> _test_elt_nil t =
>   testName "elt(a)(nil) == false" $
>   \a -> eq (elt a (nil `withTypeOf` t)) False
> 
> 
> _test_elt_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_elt_cons _ =
>   testName "elt(a)(cons(b,x)) == if(eq(a,b),true,elt(a)(x))" $
>   \a b x -> eq
>     (elt a (cons b x))
>     (if eq a b then True else elt a x)

</p></div>
</div>

Special cases.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a,b \in A$, we have $$\elt(a,\cons(b,\nil)) = \beq(a,b).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \elt(a,\cons(b,\nil)) \\
 & = & \bif(\beq(a,b),\btrue,\elt(a,\nil)) \\
 & = & \bif(\beq(a,b),\btrue,\bfalse) \\
 & = & \beq(a,b)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_elt_single :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> Bool)
> _test_elt_single t =
>   testName "elt(a)(cons(b,nil)) == eq(a,b)" $
>   \a b -> eq
>     (elt a (cons b (nil `withTypeOf` t)))
>     (eq a b)

</p></div>
</div>

$\elt$ interacts with $\cat$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have $$\elt(a)(\cat(x,y)) = \bor(\elt(a)(x),\elt(a)(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cat(x,y)) \\
 & = & \elt(a)(\cat(\nil,y)) \\
 & = & \elt(a)(y) \\
 & = & \bor(\bfalse,\elt(a)(y)) \\
 & = & \bor(\elt(a)(\nil),\elt(a)(y)) \\
 & = & \bor(\elt(a)(x),\elt(a)(y))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $y$ some $x$, and let $b \in A$. If $b = a$ we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cat(\cons(b,x),y)) \\
 & = & \elt(a)(\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(\cat(x,y))} \\
 & = & \btrue \\
 & = & \bor(\btrue,\elt(a)(y)) \\
 & = & \bor(\bif{\beq(a,b)}{\btrue}{\elt(a)(x)},\elt(a)(y)) \\
 & = & \bor(\elt(a)(\cons(b,x)),\elt(a)(y))
\end{eqnarray*}$$
as claimed. If $b \neq a$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cat(\cons(b,x),y)) \\
 & = & \elt(a)(\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(\cat(x,y))} \\
 & = & \elt(a)(\cat(x,y)) \\
 & = & \bor(\elt(a)(x),\elt(a)(y)) \\
 & = & \bor(\bif{\beq(a,b)}{\btrue}{\elt(a)(x)},\elt(a)(y)) \\'
 & = & \bor(\elt(a)(\cons(b,x)),\elt(a)(y))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_elt_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_elt_cat _ =
>   testName "elt(a)(cat(x,y)) == or(elt(a)(x),elt(a)(y))" $
>   \a x y -> eq (elt a (cat x y)) (or (elt a x) (elt a y))

</p></div>
</div>

$\elt$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$. For all $b \in A$ and $x \in \lists{A}$ we have $$\elt(a)(\snoc(b,x)) = \bif{\beq(a,b)}{\btrue}{\elt(a)(x)}.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\snoc(b,\nil)) \\
 & = & \elt(a)(\cons(b,\nil)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(\nil)}
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $b$ for some $x$, and let $c \in A$. Now
$$\begin{eqnarray*}
 &   & \elt(a)(\snoc(b,\cons(c,x))) \\
 & = & \elt(a)(\cons(c,\snoc(b,x))) \\
 & = & \bif{\beq(a,c)}{\btrue}{\elt(a)(\snoc(b,x))} \\
 & = & \bif{\beq(a,c)}{\btrue}{\bif{\beq(a,b)}{\btrue}{\elt(a)(x)}} \\
 & = & \bif{\beq(a,b)}{\btrue}{\bif{\beq(a,c)}{\btrue}{\elt(a)(x)}} \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(\cons(c,x))}
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_elt_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_elt_snoc _ =
>   testName "elt(a)(snoc(b,x)) == if(eq(a,b),true,elt(a)(x))" $
>   \a b x -> eq (elt a (snoc b x)) (if eq a b then True else elt a x)

</p></div>
</div>

$\elt$ interacts with $\rev$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\elt(a)(x) = \elt(a)(\rev(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\rev(x)) \\
 & = & \elt(a)(\rev(\nil)) \\
 & = & \elt(a)(\nil) \\
 & = & \elt(a)(x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \elt(a)(\rev(\cons(b,x))) \\
 & = & \elt(a)(\snoc(b,\rev(x))) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(\rev(x))} \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(x)} \\
 & = & \elt(a)(\cons(b,x))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_elt_rev :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_elt_rev _ =
>   testName "elt(a)(x) == elt(a)(rev(x))" $
>   \a x -> eq (elt a x) (elt a (rev x))

</p></div>
</div>

$\elt$ interacts with $\map(f)$ when $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets and suppose $f : A \rightarrow B$ is injective. Then for all $a \in A$ and $x \in \lists{A}$ we have $$\elt(a)(x) = \elt(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \elt(a)(\nil) \\
 & = & \bfalse \\
 & = & \elt(f(a),\nil) \\
 & = & \elt(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $x$ and let $b \in A$. Note that $\beq(a,b) = \beq(f(a),f(b))$. Then we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(x)} \\
 & = & \bif{\beq(f(a),f(b))}{\btrue}{\elt(f(a),\map(f)(x))} \\
 & = & \elt(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \elt(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

As a special case, the items in $\tails(x)$ and $\inits(x)$ are precisely the suffixes and prefixes of $x$, respectively.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. We have the following.

1. $\elt(y,\tails(x)) = \suffix(y,x)$.
2. $\elt(y,\inits(x)) = \prefix(y,x)$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we consider two cases. If $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \elt(y,\tails(x)) \\
 & = & \elt(\nil,\tails(\nil)) \\
 & = & \elt(\nil,\cons(\nil,\nil)) \\
 & = & \bif{\beq(\nil,\nil)}{\btrue}{\elt(\nil,\nil)} \\
 & = & \btrue \\
 & = & \prefix(\nil,\nil) \\
 & = & \prefix(\rev(\nil),\rev(\nil)) \\
 & = & \suffix(\nil,\nil) \\
 & = & \suffix(y,x)
\end{eqnarray*}$$
as claimed. Suppose $y \neq \nil$; then we have $y = \snoc(b,u)$ for some $b \in A$ and $u \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \elt(y,\tails(x)) \\
 & = & \elt(y,\tails(\nil)) \\
 & = & \elt(y,\cons(\nil,\nil)) \\
 & = & \bif{\beq(y,\nil)}{\btrue}{\elt(y,\nil)} \\
 & = & \elt(y,\nil) \\
 & = & \bfalse \\
 & = & \suffix(\snoc(b,u),\nil) \\
 & = & \suffix(y,x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $y$ for some $x$ and let $a \in A$. Again we consider two possibilities for $y$. If $y = \cons(a,x)$, we have
$$\begin{eqnarray*}
 &   & \elt(y,\tails(\cons(a,x))) \\
 & = & \elt(y,\cons(\cons(a,x),\tails(x))) \\
 & = & \bif{\beq(y,\cons(a,x)}{\btrue}{\elt(y,\tails(x)} \\
 & = & \btrue \\
 & = & \suffix(\cons(a,x),\cons(a,x)) \\
 & = & \suffix(y,\cons(a,x))
\end{eqnarray*}$$
as claimed. Suppose $y \neq \cons(a,x)$. Now
$$\begin{eqnarray*}
 &   & \elt(y,\tails(\cons(a,x))) \\
 & = & \elt(y,\cons(\cons(a,x),\tails(x))) \\
 & = & \bif{\beq(y,\cons(a,x))}{\btrue}{\elt(y,\tails(x)} \\
 & = & \elt(y,tails(x)) \\
 & = & \suffix(y,x) \\
 & = & \suffix(y,\cons(a,x))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \elt(y,\inits(x)) \\
 & = & \elt(y,\rev(\map(\rev)(\tails(\rev(x))))) \\
 & = & \elt(y,\map(\rev)(\tails(\rev(x)))) \\
 & = & \elt(\rev(y),\map(\rev)(\map(\rev)(\tails(\rev(x))))) \\
 & = & \elt(\rev(y),\map(\rev \circ \rev)(\tails(\rev(x)))) \\
 & = & \elt(\rev(y),\tails(\rev(x))) \\
 & = & \suffix(\rev(y),\rev(x)) \\
 & = & \prefix(y,x)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_elt_tails :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_elt_tails _ =
>   testName "elt(y,tails(x)) == suffix(y,x)" $
>   \x y -> eq (elt y (tails x)) (suffix y x)
> 
> 
> _test_elt_inits :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_elt_inits _ =
>   testName "elt(y,inits(x)) == prefix(y,x)" $
>   \x y -> eq (elt y (inits x)) (prefix y x)

</p></div>
</div>

If we filter $a$ out of a list, it is no longer an item there.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x \in \lists{A}$. Then $$\elt(a)(\filter(\bnot(\beq(a,-)),x)) = \bfalse.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\filter(\bnot(\beq(a,-)),\nil)) \\
 & = & \elt(a)(\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for $x$ and let $b \in A$. We have two possibilities. If $b = a$ (that is, $\bnot(\beq(a,b)) = \bfalse$), we have
$$\begin{eqnarray*}
 &   & \elt(a)(\filter(\bnot(\beq(a,-)),\cons(b,x))) \\
 & = & \elt(a)(\filter(\bnot(\beq(a,-)),x)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed. If $b \neq a$ (that is, $\bnot(\beq(a,b)) = \btrue$), we have
$$\begin{eqnarray*}
 &   & \elt(a)(\filter(\bnot(\beq(a,-)),\cons(b,x))) \\
 & = & \elt(a)(\cons(b,\filter(\bnot(\beq(a,-),x))) \\
 & = & \filter(\bnot(\beq(a,-)),x) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_elt_filter_eq :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_elt_filter_eq _ =
>   testName "elt(a)(filter(eq(a,-),x)) == false" $
>   \a x -> eq (elt a (filter (not . eq a) x)) False

</p></div>
</div>

$\elt$ is an $\any$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x \in \lists{A}$. Then $$\elt(a)(x) = \any(\beq(a,-),x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(x) \\
 & = & \elt(a)(\nil) \\
 & = & \bfalse \\
 & = & \any(\beq(a,-),\nil) \\
 & = & \any(\beq(a,-),x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(x)} \\
 & = & \bif{\btrue}{\btrue}{\elt(a)(x)} \\
 & = & \btrue \\
 & = & \bor(\btrue,\any(\beq(a,-),x)) \\
 & = & \bor(\beq(a,b),\any(\beq(a,-),x)) \\
 & = & \any(\beq(a,-),\cons(b,x))
\end{eqnarray*}$$
as needed. If $a \neq b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \elt(a)(\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a)(x)} \\
 & = & \bif{\bfalse}{\btrue}{\elt(a)(x)} \\
 & = & \elt(a)(x) \\
 & = & \any(\beq(a,-),x) \\
 & = & \bor(\bfalse,\any(\beq(a,-),x)) \\
 & = & \bor(\beq(a,b),\any(\beq(a,-),x)) \\
 & = & \any(\beq(a,-),\cons(b,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_elt_any :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_elt_any _ =
>   testName "elt(a)(x) == any(eq(a,-))(x)" $
>   \a x -> eq (elt a x) (any (eq a) x)

</p></div>
</div>

$\elt$ can detect when two lists are distinct.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x,y \in \lists{A}$. If $\elt(a)(x) \neq \elt(a)(y)$, then $x \neq y$.
</p></div>

<div class="proof"><p>
The contrapositive of this statement is trivial and kind of silly looking: If $x = y$, then $\elt(a)(x) = \elt(a)(y)$. But notice that this theorem gives us a simple way to detect when two lists are distinct from each other.
</p></div>

<div class="test"><p>

> _test_elt_distinct :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_elt_distinct _ =
>   testName "if elt(a)(x) /= elt(a)(y) then x /= y" $
>   \a x y -> if not (eq (elt a x) (elt a y))
>     then not (eq x y)
>     else True

</p></div>
</div>

$\elt$ interacts with $\map(f)$ when $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ injective. For all $a \in A$ and $x \in  \lists{A}$, we have $$\elt(a,x) = \elt(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\nil) \\
 & = & \bfalse \\
 & = & \elt(f(a),\nil) \\
 & = & \elt(f(a),\map(f)(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Note that $\beq(a,b) = \beq(f(a),f(b))$, so we have
$$\begin{eqnarray*}
 &   & \elt(a,\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\btrue}{\elt(a,x)} \\
 & = & \bif{\beq(f(a),f(b))}{\btrue}{\elt(f(a),\map(f)(x))} \\
 & = & \elt(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \elt(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\elt$ interacts with $\range$.

<div class="result">
<div class="thm"><p>
Let $a,b,c \in \nats$. If $\nleq(a,c)$, then $$\elt(a,\range(\next(c),b)) = \bfalse.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $b$. If $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \elt(a,\range(\next(c),\zero)) \\
 & = & \elt(a,\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equation holds for all $a$ and $c$ for some $b$. Suppose $\nleq(a,c)$; then $\nleq(a,\next(c))$. Now
$$\begin{eqnarray*}
 &   & \elt(a,\range(\next(c),\next(b))) \\
 & = & \elt(a,\cons(\next(c),\range(\next(\next(c)),b))) \\
 & = & \bif{\beq(a,\next(c))}{\btrue}{\elt(a,\range(\next(\next(c)),b))} \\
 & = & \elt(a,\range(\next(\next(c)),b)) \\
 & = & \bfalse
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_elt_range :: (List t, Natural n, Equal n)
>   => t a -> n -> Test (t n -> n -> n -> n -> Bool)
> _test_elt_range _ _ =
>   testName "if leq(a,c) then eq(elt(a,range(next(c),b)),false)" $
>   \t a b c -> if leq a c
>     then eq (elt a ((range (next c) b) `withTypeOf` t)) False
>     else True

</p></div>
</div>


Testing
-------

Suite:

> _test_elt ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Arbitrary (t n), Show (t n), Equal (t n)
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a))
>   , TypeName n, Equal n, Show n, Arbitrary n, Natural n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_elt t n maxSize numCases = do
>   testLabel1 "elt" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_elt_nil t)
>   runTest args (_test_elt_cons t)
>   runTest args (_test_elt_single t)
>   runTest args (_test_elt_cat t)
>   runTest args (_test_elt_snoc t)
>   runTest args (_test_elt_rev t)
>   runTest args (_test_elt_tails t)
>   runTest args (_test_elt_inits t)
>   runTest args (_test_elt_filter_eq t)
>   runTest args (_test_elt_any t)
>   runTest args (_test_elt_distinct t)
>   runTest args (_test_elt_range t n)

Main:

> main_elt :: IO ()
> main_elt = do
>   _test_elt (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_elt (nil :: ConsList Unary) (zero :: Unary) 20 100
