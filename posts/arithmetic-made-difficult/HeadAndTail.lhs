---
title: Head and Tail
author: nbloomf
date: 2018-01-03
tags: arithmetic-made-difficult, literate-haskell
---

> module HeadAndTail (
>   head, tail, isNil, _test_head_tail, main_head_tail
> ) where
> 
> import Prelude ()
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers
> import Lists

We define some helper functions in terms of $\uncons$, analogous to $\prev$ and $\iszero$ on $\nats$. These do not require recursion.

<div class="result">
<div class="dfn"><p>
Let $A$ be a set. We define $\isnil : \lists{A} \rightarrow \bool$ by $$\isnil = \either(\const(\btrue),\const(\bfalse)) \circ \uncons$$ and $\head : \lists{A} \rightarrow 1 + A$ by $$\head = \uPair(\id,\fst) \circ \uncons$$ and $\tail : \lists{A} \rightarrow \lists{A}$ by $$\tail = \either(\const(\nil),\snd) \circ \uncons.$$

In Haskell:

> isNil :: (List t) => t a -> Bool
> isNil = (either (const True) (const False)) . uncons
> 
> 
> head :: (List t) => t a -> Either () a
> head = (upair id fst) . uncons
> 
> 
> tail :: (List t) => t a -> t a
> tail = (either (const nil) snd) . uncons

</p></div>
</div>

Now $\isnil$ detects $\nil$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have the following.

1. $\isnil(\nil) = \btrue$.
2. $\isnil(\cons(a,x)) = \bfalse$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \isnil(\nil) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\uncons(\nil)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\lft(\ast)) \\
 & = & \const(\btrue)(\ast) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \isnil(\cons(a,x)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\uncons(\cons(a,x))) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\rgt((a,x))) \\
 & = & \const(\bfalse)((a,x)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="thm"><p>

> _test_isNil_nil :: (List t, Equal (t a))
>   => t a -> Test Bool
> _test_isNil_nil z =
>   testName "isNil(nil) == true" $
>   let nil' = nil `withTypeOf` z in
>   isNil nil'
> 
> 
> _test_isNil_cons :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_isNil_cons z =
>   testName "isNil(cons(a,x)) == false" $
>   \a x -> eq (isNil (cons a x)) False

</p></div>
</div>

$\head$ extracts the "first" entry of a list:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have the following.

1. $\head(\nil) = \lft(\ast)$.
2. $\head(\cons(a,x)) = \rgt(a)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \head(\nil) \\
 & = & \uPair(\id,\fst)(\uncons(\nil)) \\
 & = & \uPair(\id,\fst)(\lft(\ast)) \\
 & = & \lft(\id(\ast)) \\
 & = & \lft(\ast)
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \head(\cons(a,x)) \\
 & = & \upair(\id,\fst)(\uncons(\cons(a,x))) \\
 & = & \upair(\id,\fst)(\rgt((a,x))) \\
 & = & \rgt(\fst((a,x))) \\
 & = & \rgt(a)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="thm"><p>

> _test_head_nil :: (List t, Equal (t a), Equal a)
>   => t a -> Test Bool
> _test_head_nil z =
>   testName "head(nil) == lft(*)" $
>   let nil' = nil `withTypeOf` z in
>   eq (head nil') (lft ())
> 
> 
> _test_head_cons :: (List t, Equal (t a), Equal a)
>   => t a -> Test (a -> t a -> Bool)
> _test_head_cons z =
>   testName "head(cons(a,x)) == rgt(a)" $
>   \a x -> eq (head (cons a x)) (rgt a)

</p></div>
</div>

And $\tail$ peels off the "first" entry of a list.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have the following.

1. $\tail(\nil) = \nil$.
2. $\tail(\cons(a,x)) = x$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \tail(\nil) \\
 & = & \either(\const(\nil),\snd)(\uncons(\nil)) \\
 & = & \either(\const(\nil),\snd)(\lft(\ast)) \\
 & = & \const(\nil)(\ast) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \tail(\cons(a,x)) \\
 & = & \either(\const(\nil),\snd)(\uncons(\cons(a,x))) \\
 & = & \either(\const(\nil),\snd)(\rgt((a,x))) \\
 & = & \snd((a,x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="thm"><p>

> _test_tail_nil :: (List t, Equal (t a))
>   => t a -> Test Bool
> _test_tail_nil z =
>   testName "tail(nil) == tail" $
>   let nil' = nil `withTypeOf` z in
>   eq (tail nil') nil'
> 
> 
> _test_tail_cons :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_tail_cons z =
>   testName "tail(cons(a,x)) == x" $
>   \a x -> eq (tail (cons a x)) x

</p></div>
</div>

While we're at it, no cons can be its own tail.

<div class="result">
<div class="thm">
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then $\cons(a,x) \neq x$.
</div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have $\nil \neq \cons(a,\nil)$ for all $a$ as needed. For the inductive step, suppose the inequality holds for some $x$ and let $b \in A$. Suppose further by way of contradiction that $\cons(b,x) = \cons(a,\cons(b,x))$. Then we have $a = b$ and $x = \cons(b,x)$, a contradiction. So in fact $\cons(b,x) \neq \cons(a,\cons(b,x))$ as needed.
</p></div>

<div class="test"><p>

> _test_cons_self :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_cons_self _ =
>   testName "x /= cons(a,x)" $
>   \a x -> not (eq (cons a x) x)

</p></div>
</div>


Testing
-------

Suite:

> _test_head_tail ::
>   ( TypeName a, Equal a, Show a, Arbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_head_tail t maxSize numCases = do
>   testLabel ("head and tail: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_isNil_nil t)
>   runTest args (_test_isNil_cons t)
>   runTest args (_test_head_nil t)
>   runTest args (_test_head_cons t)
>   runTest args (_test_tail_nil t)
>   runTest args (_test_tail_cons t)
>   runTest args (_test_cons_self t)

Main:

> main_head_tail :: IO ()
> main_head_tail = do
>   _test_head_tail (nil :: ConsList Bool)  20 100
>   _test_head_tail (nil :: ConsList Unary) 20 100