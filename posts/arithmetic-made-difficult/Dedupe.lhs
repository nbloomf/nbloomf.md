---
title: Dedupe
author: nbloomf
date: 2017-05-28
tags: arithmetic-made-difficult, literate-haskell
slug: dedupe
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Dedupe
>   ( dedupeL, dedupeR, _test_dedupe, main_dedupe
>   ) where
> 
> import Testing
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> import Lists
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Select
> import Unique
> import Delete

Today we'll define a function ``dedupe`` which removes any "duplicate" items in a list. Before jumping in, let's think a little about what such a function should do. For example, say we run ``dedupe`` on the list $$\langle a, b, a, c, a \rangle.$$ The item $a$ appears three times, so after deduplicating it should only appear once. We'd prefer not to change the relative order of items in the list, so all we can do is remove two of the $a$s. There are three ways to do this, resulting in either $$\langle a, b, c \rangle,$$ $$\langle b, a, c \rangle,$$ or $$\langle b, c, a \rangle.$$ That is, we can keep the *first* copy of $a$, the *last* copy, or *some middle* copy. It seems to me that keeping some middle copy is not the most general solution. If an item appears only twice, there is no middle appearance, and if an item appears more than three times then there is no *unique* middle appearance to keep. So it appears the two most general options are to keep the first copy of an item or to keep the last copy. We will call these strategies $\dedupeL$ (**dedup**licate from the **L**eft) and $\dedupeR$ (**dedup**licate from the **R**ight), respectively. We'll see that these two options are related. We'll start with $\dedupeL$.

We want to implement $\dedupeL$ as either a right fold or a left fold. But which one? Say our input list is $$x = \langle a, b, c \rangle.$$ Note that $\foldr{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(a, \varphi(b, \varphi(c, \varepsilon))),$$ while $\foldl{\varepsilon}{\varphi}(x)$ will expand into $$\varphi(c, \varphi(b, \varphi(a, \varepsilon))).$$ Note that $\dedupeL$ has to process the entire input list, so both of these computations will evaluate completely from the inside out. So which one makes more sense, keeping in mind that $\dedupeL$ needs to detect the *first* appearance of each item?

With this handwavy mess in mind, we define $\dedupeL$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varphi : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(a,x) = \cons(a,\delete(a,x)).$$ Now define $\dedupeL : \lists{A} \rightarrow \lists{A}$ by $$\dedupeL(x) = \foldr{\nil}{\varphi}(x).$$

In Haskell:

> dedupeL :: (List t, Equal a) => t a -> t a
> dedupeL = foldr nil phi
>   where
>     phi a x = cons a (delete a x)

</p></div>
</div>

Since $\dedupeL$ is defined as a foldr, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. $\dedupeL$ is the unique map $f : \lists{A} \rightarrow \lists{A}$ satisfying the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{eqnarray*}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \cons(a,\delete(a)(f(x)))
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_dedupeL_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test Bool
> _test_dedupeL_nil t =
>   testName "dedupeL(nil) == nil" $
>   eq (dedupeL nil) (nil `withTypeOf` t)
> 
> 
> _test_dedupeL_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_dedupeL_cons _ =
>   testName "dedupeL(cons(a,x)) == cons(a,delete(a)(dedupeL(x))" $
>   \a x -> eq (dedupeL (cons a x)) (cons a (delete a (dedupeL x)))

</p></div>
</div>

Now $\dedupeL$ and $\delete$ commute.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a \in A$ and $x \in \lists{A}$. Then $$\delete(a,\dedupeL(x)) = \dedupeL(\delete(a,x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\nil)) \\
 & = & \delete(a,\nil) \\
 & = & \nil \\
 & = & \dedupeL(\nil) \\
 & = & \dedupeL(\delete(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$ and let $b \in A$. We consider two possibilities. If $b = a$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\cons(b,x))) \\
 & = & \delete(a,\cons(b,\delete(b,\dedupeL(x)))) \\
 & = & \delete(a,\delete(b,\dedupeL(x))) \\
 & = & \delete(a,\delete(a,\dedupeL(x))) \\
 & = & \delete(a,\dedupeL(x)) \\
 & = & \dedupeL(\delete(a,x)) \\
 & = & \dedupeL(\delete(a,\cons(a,x))) \\
 & = & \dedupeL(\delete(a,\cons(b,x)))
\end{eqnarray*}$$
as needed. Suppose instead that $b \neq a$. Now we have
$$\begin{eqnarray*}
 &   & \delete(a,\dedupeL(\cons(b,x))) \\
 & = & \delete(a,\cons(b,\delete(b,\dedupeL(x)))) \\
 & = & \cons(b,\delete(a,\delete(b,\dedupeL(x)))) \\
 & = & \cons(b,\delete(b,\delete(a,\dedupeL(x)))) \\
 & = & \cons(b,\delete(b,\dedupeL(\delete(a,x)))) \\
 & = & \dedupeL(\cons(b,\delete(a,x))) \\
 & = & \dedupeL(\delete(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_dedupeL_delete :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_dedupeL_delete _ =
>   testName "dedupeL(delete(a,x)) == delete(a,dedupeL(x))" $
>   \a x -> eq (dedupeL (delete a x)) (delete a (dedupeL x))

</p></div>
</div>

$\dedupeL$s are $\unique$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$. Then $\unique(\dedupeL(x)) = \btrue$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \unique(\dedupeL(\nil)) \\
 & = & \unique(\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have $\unique(\dedupeL(x)) = \btrue$, so that $\unique(\delete(a,\dedupeL(x))) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \unique(\dedupeL(\cons(a,x))) \\
 & = & \unique(\cons(a,\delete(a,\dedupeL(x)))) \\
 & = & \band(\bnot(\elt(a,\delete(a,\dedupeL(x)))),\unique(\delete(a,\dedupeL(x)))) \\
 & = & \band(\btrue,\unique(\delete(a,\dedupeL(x)))) \\
 & = & \unique(\delete(a,\dedupeL(x))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_dedupeL_unique :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_dedupeL_unique _ =
>   testName "unique(dedupeL(x)) == true" $
>   \x -> unique (dedupeL x)

</p></div>
</div>

$\dedupeL$ preserves $\prefix$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. If $\prefix(x,y) = \btrue$ then $\prefix(\dedupeL(x),\dedupeL(y)) = \btrue$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that $$\prefix(x,y) = \prefix(\nil,y) = \btrue$$ and
$$\begin{eqnarray*}
 &   & \prefix(\dedupeL(x),\dedupeL(y)) \\
 & = & \prefix(\dedupeL(\nil),\dedupeL(y)) \\
 & = & \prefix(\nil,\dedupeL(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for all $y$ for some $x$ and let $a \in A$. Suppose further that $\prefix(\cons(a,x),y) = \btrue$. Now we must have $y = \cons(a,u)$ where $\prefix(x,u) = \btrue$. Using the inductive hypothesis, we have $$\prefix(\dedupeL(x),\dedupeL(u)) = \btrue,$$ so that $$\prefix(\delete(a,\dedupeL(x)),\delete(a,\dedupeL(u))) = \btrue.$$ Now
$$\begin{eqnarray*}
 &   & \prefix(\dedupeL(\cons(a,x)),\dedupeL(y)) \\
 & = & \prefix(\dedupeL(\cons(a,x)),\dedupeL(\cons(a,u))) \\
 & = & \prefix(\cons(a,\delete(a,\dedupeL(x))),\cons(a,\delete(a,\dedupeL(u)))) \\
 & = & \prefix(\delete(a,\dedupeL(x)),\delete(a,\dedupeL(u))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_dedupeL_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_dedupeL_prefix _ =
>   testName "prefix(x,y) ==> prefix(dedupeL(x),dedupeL(y))" $
>   \x y -> if prefix x y
>     then prefix (dedupeL x) (dedupeL y)
>     else True

</p></div>
</div>

$\dedupeL$ fixes $\unique$s.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x \in \lists{A}$. Then $\beq(x,\dedupeL(x)) = \unique(x)$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(x,\dedupeL(x)) \\
 & = & \beq(\nil,\dedupeL(\nil)) \\
 & = & \beq(\nil,\nil) \\
 & = & \btrue \\
 & = & \unique(\nil) \\
 & = & \unique(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$.
$$\begin{eqnarray*}
 &   & \beq(\cons(a,x),\dedupeL(\cons(a,x))) \\
 & = & \beq(\cons(a,x),\cons(a,\delete(a,\dedupeL(x)))) \\
 & = & \band(\beq(a,a),\beq(x,\delete(a,\dedupeL(x)))) \\
 & = & \band(\btrue,\beq(x,\delete(a,\dedupeL(x)))) \\
 & = & \beq(x,\delete(a,\dedupeL(x))) \\
 & = & \beq(x,\dedupeL(\delete(a,x))) \\
 & = & Q.
\end{eqnarray*}$$
We now consider two possibilities. If $\elt(a,x) = \bfalse$, then $$\beq(x,\delete(a,x)) = \bnot(\elt(a,x)) = \btrue,$$ and using the inductive hypothesis on $x$ we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \beq(x,\dedupeL(x)) \\
 & = & \unique(x) \\
 & = & \band(\btrue,\unique(x)) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
\end{eqnarray*}$$
as needed. Suppose instead that $\elt(a,x) = \btrue$. Note that
$$\begin{eqnarray*}
 &   & \elt(a,\dedupeL(\delete(a,x))) \\
 & = & \elt(a,\delete(a,\dedupeL(x))) \\
 & = & \bfalse,
\end{eqnarray*}$$
so that $\beq(x,\dedupeL(\delete(a,x))) = \bfalse$. Now
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bfalse \\
 & = & \band(\bfalse,\unique(x)) \\
 & = & \band(\bnot(\elt(a,x)),\unique(x)) \\
 & = & \unique(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_dedupeL_eq_unique :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_dedupeL_eq_unique _ =
>   testName "eq(x,dedupeL(x)) == unique(x)" $
>   \x -> eq (eq x (dedupeL x)) (unique x)

</p></div>
</div>

$\dedupeL$ is idempotent.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set and $x \in \lists{A}$. Then $\dedupeL(\dedupeL(x)) = \dedupeL(x)$.
</p></div>

<div class="proof"><p>
Note that $\unique(\dedupeL(x)) = \btrue$, so that $\dedupeL(\dedupeL(x)) = \dedupeL(x)$ as claimed.
</p></div>

<div class="test"><p>

> _test_dedupeL_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_dedupeL_idempotent _ =
>   testName "dedupeL(dedupeL(x)) == dedupeL(x)" $
>   \x -> eq (dedupeL (dedupeL x)) (dedupeL x)

</p></div>
</div>

$\dedupeL$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have $$\dedupeL(\snoc(a,x)) = \bif{\elt(a,x)}{\dedupeL(x)}{\snoc(a,\dedupeL(x))}.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \dedupeL(\snoc(a,\nil)) \\
 & = & \dedupeL(\cons(a,\nil)) \\
 & = & \cons(a,\nil) \\
 & = & \bif{\bfalse}{\nil}{\cons(a,\nil)} \\
 & = & \bif{\elt(a,\nil)}{\nil}{\cons(a,\nil)} \\
 & = & \bif{\elt(a,\nil)}{\dedupeL(\nil)}{\snoc(a,\nil)}
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \dedupeL(\snoc(a,\cons(b,x))) \\
 & = & \dedupeL(\cons(b,\snoc(a,x))) \\
 & = & \cons(b,\delete(b)(\dedupeL(\snoc(a,x)))) \\
 & = & \cons(b,\delete(b)(\bif{\elt(a,x)}{\dedupeL(x)}{\snoc(a,\dedupeL(x))})) \\
 & = & \bif{\elt(a,x)}{\cons(b,\delete(b)(\dedupeL(x)))}{\cons(b,\delete(b)(\snoc(a,\dedupeL(x))))} \\
 & = & \bif{\elt(a,x)}{\dedupeL(\cons(b,x))}{\cons(b,\delete(b)(\snoc(a,\dedupeL(x))))} \\
 & = & \bif{\elt(a,x)}{\dedupeL(\cons(b,x))}{\cons(b,\bif{\beq(a,b)}{\delete(b)(\dedupeL(x))}{\snoc(a,\delete(b)(\dedupeL(x))})} \\
 & = & \bif{\elt(a,x)}{\dedupeL(\cons(b,x))}{\bif{\beq(a,b)}{\cons(b,\delete(b)(\dedupeL(x)))}{\cons(b,\snoc(a,\delete(b)(\dedupeL(x)))}} \\
 & = & \bif{\elt(a,x)}{\dedupeL(\cons(b,x))}{\bif{\beq(a,b)}{\dedupeL(\cons(b,x))}{\cons(b,\snoc(a,\delete(b)(\dedupeL(x)))}} \\
 & = & \bif{\bor(\beq(a,b),\elt(a,x))}{\dedupe(\cons(b,x))}{\cons(b,\snoc(a,\delete(b)(\dedupeL(x))))} \\
 & = & \bif{\elt(a,\cons(b,x)}{\dedupe(\cons(b,x))}{\cons(b,\snoc(a,\delete(b)(\dedupeL(x))))} \\
 & = & \bif{\elt(a,\cons(b,x)}{\dedupe(\cons(b,x))}{\snoc(a,\cons(b,\delete(b)(\dedupeL(x))))} \\
 & = & \bif{\elt(a,\cons(b,x)}{\dedupe(\cons(b,x))}{\snoc(a,\dedupeL(\cons(b,x)))}
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_dedupeL_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_dedupeL_snoc _ =
>   testName "dedupeL(snoc(a,x)) == if(elt(a,x),dedupeL(x),snoc(a,dedupeL(x)))" $
>   \a x -> eq
>     (dedupeL (snoc a x))
>     (if elt a x then dedupeL x else snoc a (dedupeL x))

</p></div>
</div>

We define $\dedupeR$ in terms of $\dedupeL$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\dedupeL : \lists{A} \rightarrow \lists{A}$ by $$\dedupeL(x) = \rev(\dedupeR(\rev(x))).$$

In Haskell:

> dedupeR :: (List t, Equal a) => t a -> t a
> dedupeR = rev . dedupeL . rev

</p></div>
</div>

The defining equations for $\dedupeL$ have equivalents for $\dedupeR$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have the following.

1. $\dedupeR(\nil) = \nil$.
2. $\dedupeR(\snoc(a,x)) = \snoc(a,\delete(a,\dedupeR(x)))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \dedupeR(\nil) \\
 & = & \rev(\dedupeL(\rev(\nil))) \\
 & = & \rev(\dedupeL(\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as needed.
2. Note that
$$\begin{eqnarray*}
 &   & \dedupeR(\snoc(a,x)) \\
 & = & \rev(\dedupeL(\rev(\snoc(a,x)))) \\
 & = & \rev(\dedupeL(\cons(a,\rev(x)))) \\
 & = & \rev(\cons(a,\delete(a,\dedupeL(\rev(x))))) \\
 & = & \snoc(a,\rev(\delete(a,\dedupeL(\rev(x))))) \\
 & = & \snoc(a,\delete(a,\rev(\dedupeL(\rev(x))))) \\
 & = & \snoc(a,\delete(a,\dedupeR(x)))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_dedupeR_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test Bool
> _test_dedupeR_nil t =
>   testName "dedupeR(nil) == nil" $
>   eq (dedupeR nil) (nil `withTypeOf` t)
> 
> 
> _test_dedupeR_snoc :: (List t, Equal a, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_dedupeR_snoc _ =
>   testName "dedupeR(snoc(a,x)) == snoc(a,delete(a)(dedupeR(x))" $
>   \a x -> eq (dedupeR (snoc a x)) (snoc a (delete a (dedupeR x)))

</p></div>
</div>

$\dedupeR$s are unique.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$. Then $\unique(\dedupeR(x)) = \btrue$.
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \unique(\dedupeR(x)) \\
 & = & \unique(\rev(\dedupeL(\rev(x)))) \\
 & = & \unique(\dedupeL(\rev(x))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_dedupeR_unique :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_dedupeR_unique _ =
>   testName "unique(dedupeR(x)) == true" $
>   \x -> eq (unique (dedupeR x)) True

</p></div>
</div>

$\dedupeR$ is idempotent.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$. Then $\dedupeR(\dedupeR(x)) = \dedupeR(x)$.
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \dedupeR \circ \dedupeR \\
 & = & \rev \circ \dedupeL \circ \rev \circ \rev \circ \dedupeL \circ \rev \\
 & = & \rev \circ \dedupeL \circ \dedupeL \circ \rev \\
 & = & \rev \circ \dedupeL \circ \rev \\
 & = & \dedupeR
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_dedupeR_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_dedupeR_idempotent _ =
>   testName "dedupeR(dedupeR(x)) == dedupeR(x)" $
>   \x -> eq (dedupeR (dedupeR x)) (dedupeR x)

</p></div>
</div>


Testing
-------

Suite:

> _test_dedupe ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => t a -> Int -> Int -> IO ()
> _test_dedupe t maxSize numCases = do
>   testLabel1 "dedupeL & dedupeR" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_dedupeL_nil t)
>   runTest args (_test_dedupeL_cons t)
>   runTest args (_test_dedupeL_delete t)
>   runTest args (_test_dedupeL_unique t)
>   runTest args (_test_dedupeL_prefix t)
>   runTest args (_test_dedupeL_eq_unique t)
>   runTest args (_test_dedupeL_idempotent t)
>   runTest args (_test_dedupeL_snoc t)
> 
>   runTest args (_test_dedupeR_nil t)
>   runTest args (_test_dedupeR_snoc t)
>   runTest args (_test_dedupeR_unique t)
>   runTest args (_test_dedupeR_idempotent t)

Main:

> main_dedupe :: IO ()
> main_dedupe = do
>   _test_dedupe (nil :: ConsList Bool)  50 500
>   _test_dedupe (nil :: ConsList Unary) 50 500
