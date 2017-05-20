---
title: Reverse
author: nbloomf
date: 2017-04-24
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Reverse
>   ( snoc, foldl, rev, _test_rev, main_rev
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import Lists
> 
> import Prelude ()
> import Test.QuickCheck

In the last post we defined a set $\lists{A}$ with a special element $\nil$, a map $\cons : A \times \lists{A} \rightarrow \lists{A}$, and a universal map $\foldr{\ast}{\ast}$. As you might guess we'll be thinking of the elements of $\lists{A}$ as finite lists, and they will form a simple kind of data structure.

In this post we'd like to address the following.

1. The $\cons$ function attaches a new item to the "beginning" of a list; we want an analogous function that attaches items to the "end".
2. We want a function that takes a list and reverses the order of its elements; say, to turn $(a,b,c)$ into $(c,b,a)$ and vice versa.
3. We want to get as close as possible to a tail recursive implementation of $\foldr{\ast}{\ast}$.

First let's tackle adding items to the end of a list; traditionally this operator is called $\snoc$ as a bad pun on "reverse $\cons$". Now the signature of $\snoc$ should be something like $$\snoc : A \times \lists{A} \rightarrow \lists{A},$$ and $\foldr{e}{\varphi}$ can be used to build a map $\lists{A} \rightarrow \lists{A}$, provided $e$ is in $\lists{A}$ and $\varphi : A \times \lists{A} \rightarrow \lists{A}$. Considering the behavior we want $\snoc$ to have, we define the following.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We now define a map $\snoc : A \times \lists{A} \rightarrow \lists{A}$ by $$\snoc(a,x) = \foldr{\cons(a,\nil)}{\cons}(x).$$

In Haskell:

> snoc :: (List t) => a -> t a -> t a
> snoc a = foldr (cons a nil) cons

</p></div>
</div>

Special cases:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $a \in A$ we have $$\snoc(a,\nil) = \cons(a,\nil).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \snoc(a,\nil) \\
 & = & \foldr{\cons(a,\nil)}{\cons}(\nil) \\
 & = & \cons(a,\nil)
\end{eqnarray*}$$
by the universal property of $\foldr{\ast}{\ast}$.
</p></div>
</div>

Now $\snoc$ and $\cons$ commute in an appropriate sense:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a,b \in A$, and let $x \in \lists{A}$. Then $$\snoc(a,\cons(b,x)) = \cons(b,\snoc(a,x)).$$
</p></div>

<div class="proof"><p>
Falls out of $\foldr{\ast}{\ast}$: we have
$$\begin{eqnarray*}
 &   & \snoc(a,\cons(b,x)) \\
 & = & \foldr{\cons(a,\nil)}{\cons}(\cons(b,x)) \\
 & = & \cons(b,\foldr{\cons(a,\nil)}{\cons}(x)) \\
 & = & \cons(b,\snoc(a,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\snoc$ interacts with $\foldr{\ast}{\ast}$.

<div class="result">
<div class="lemma"><p>
Let $A$ and $B$ be sets with $e \in B$ and $\varphi : A \times B \rightarrow B$. Then for all $a \in A$ and $x \in \lists{A}$ we have $$\foldr{e}{\varphi}(\snoc(a,x)) = \foldr{\varphi(a,e)}{\varphi}(x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\snoc(a,\nil)) \\
 & = & \foldr{e}{\varphi}(\cons(a,\nil)) \\
 & = & \varphi(a,\foldr{e}{\varphi}(\nil)) \\
 & = & \varphi(a,e) \\
 & = & \foldr{\varphi(a,e)}{\varphi}(\nil)
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x \in \lists{A}$. Now
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\snoc(a,\cons(b,x))) \\
 & = & \foldr{e}{\varphi}(\cons(b,\snoc(a,x))) \\
 & = & \varphi(b,\foldr{e}{\varphi}(\snoc(a,x))) \\
 & = & \varphi(b,\foldr{\varphi(a,e)}{\varphi}(x)) \\
 & = & \foldr{\varphi(a,e)}{\varphi}(\cons(b,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Next we define list reversal as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We now define a map $\rev : \lists{A} \rightarrow \lists{A}$ by $$\rev = \foldr{\nil}{\snoc}.$$

In Haskell:

> rev' :: (List t) => t a -> t a
> rev' = foldr nil snoc

</p></div>
</div>

Special cases:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $a,b \in A$ we have the following.

1. $\rev(\nil) = \nil$.
2. $\rev(\cons(a,\nil)) = \cons(a,\nil)$.
3. $\rev(\cons(a,\cons(b,\nil))) = \cons(b,\cons(a,\nil))$.
</p></div>

<div class="proof"><p>
1. Follows from the universal property of $\foldr{\ast}{\ast}$.
2. Note that
$$\begin{eqnarray*}
 &   & \rev(\cons(a,\nil)) \\
 & = & \foldr{\nil}{\snoc}(\cons(a,\nil)) \\
 & = & \snoc(a,\foldr{\nil}{\snoc}(\nil)) \\
 & = & \snoc(a,\nil) \\
 & = & \cons(a,\nil)
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \rev(\cons(a,\cons(b,\nil))) \\
 & = & \foldr{\nil}{\snoc}(\cons(a,\cons(b,\nil))) \\
 & = & \snoc(a,\foldr{\nil}{\snoc}(\cons(b,\nil))) \\
 & = & \snoc(a,\rev(\cons(b,\nil))) \\
 & = & \snoc(a,\cons(b,\nil)) \\
 & = & \foldr{\cons(a,\nil)}{\cons}(\cons(b,\nil)) \\
 & = & \cons(b,\foldr{\cons(a,\nil)}{\cons}(\nil)) \\
 & = & \cons(b,\cons(a,\nil))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now $\rev$, $\snoc$, and $\cons$ interact:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. Then for all $a \in A$ and $x \in \lists{A}$, we have $$\rev(\snoc(a,x)) = \cons(a,\rev(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \rev(\snoc(a,\nil)) \\
 & = & \rev(\cons(a,\nil)) \\
 & = & \snoc(a,\rev(\nil)) \\
 & = & \snoc(a,\nil) \\
 & = & \cons(a,\nil) \\
 & = & \cons(a,\rev(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \rev(\snoc(a,\cons(b,x))) \\
 & = & \rev(\cons(b,\snoc(a,x))) \\
 & = & \snoc(b,\rev(\snoc(a,x))) \\
 & = & \snoc(b,\cons(a,\rev(x))) \\
 & = & \cons(a,\snoc(b,\rev(x))) \\
 & = & \cons(a,\rev(\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\rev$ is an involution.

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $\rev(\rev(x)) = x$.
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \rev(\rev(\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \rev(\rev(\cons(a,x))) \\
 & = & \rev(\snoc(a,\rev(x))) \\
 & = & \cons(a,\rev(\rev(x))) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally, we can perform case analysis on lists with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and let $x \in \lists{A}$. Then either $x = \nil$ or $x = \snoc(a,w)$ for some $w \in \lists{A}$ and $a \in A$.
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, the conclusion holds trivially. For the inductive step, suppose the conclusion holds for some $x$ and let $a \in A$. Now $\cons(a,x) \neq \nil$. We have two cases for $x$; if $x = \nil$, then $$\cons(a,x) = \cons(a,\nil) = \snoc(a,\nil)$$ as needed. Suppose instead that $x \neq \nil$; by the inductive hypothesis we have $x = \snoc(b,w)$ for some $b \in A$ and $w \in \lists{A}$. Then we have
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cons(a,\snoc(b,w)) \\
 & = & \snoc(b,\cons(a,w))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


The Other Fold
--------------

We are now prepared to define an alternate fold, this one tail recursive. We call this one $\foldl{\ast}{\ast}$ because it processes the elements of a list "from left to right", as opposed to $\foldr{\ast}{\ast}$ which goes "from right to left".

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets, with $e \in B$ and $\varphi : A \times B \rightarrow B$. We define a map $\foldl{e}{\varphi} : \lists{A} \rightarrow B$ by $$\foldl{e}{\varphi}(x) = \foldr{e}{\varphi}(\rev(x)).$$

In Haskell:

> foldl' :: (List t) => b -> (a -> b -> b) -> t a -> b
> foldl' e phi = (foldr e phi) . rev'

</p></div>
</div>

At first this seems like a minor adjustment. But note:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, let $e \in B$, and let $\varphi : A \times B \rightarrow B$. For all $a \in A$ and $x \in \lists{A}$ we have the following.

1. $\foldl{e}{\varphi}(\nil) = e$.
2. $\foldl{e}{\varphi}(\cons(a,x)) = \foldl{\varphi(a,e)}{\varphi}(x)$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \foldl{e}{\varphi}(\nil) \\
 & = & \foldr{e}{\varphi}(\rev(\nil)) \\
 & = & \foldr{e}{\varphi}(\nil) \\
 & = & e
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \foldl{e}{\varphi}(\cons(a,x)) \\
 & = & \foldr{e}{\varphi}(\rev(\cons(a,x))) \\
 & = & \foldr{e}{\varphi}(\snoc(a,\rev(x))) \\
 & = & \foldr{\varphi(a,e)}{\varphi}(\rev(x)) \\
 & = & \foldl{\varphi(a,e)}{\varphi}(x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

This theorem says that $\foldl{\ast}{\ast}$ is naturally tail recursive like so:

> foldl :: (List t) => b -> (a -> b -> b) -> t a -> b
> foldl !e phi x = case listShape x of
>   Nil       -> e
>   Cons a as -> foldl (phi a e) phi as

Now $\foldl{\ast}{\ast}$ interacts with $\snoc$:

<div class="result">
<div class="thm"><p>
We have $$\foldl{e}{\varphi}(\snoc(a,x)) = \varphi(a,\foldl{e}{\varphi}(x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \foldl{e}{\varphi}(\snoc(a,x)) \\
 & = & \foldr{e}{\varphi}(\rev(\snoc(a,x))) \\
 & = & \foldr{e}{\varphi}(\cons(a,\rev(x)) \\
 & = & \varphi(a,\foldr{e}{\varphi}(\rev(x)) \\
 & = & \varphi(a,\foldl{e}{\varphi}(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now many list functions can be implemented in terms of either $\foldr{\ast}{\ast}$ or $\foldl{\ast}{\ast}$, and depending on the function, one may be preferable over the other. For example, we will prefer the following implementation of $\rev$.

<div class="result">
<div class="thm"><p>
We have $\rev = \foldl{\nil}{\cons}$.

In Haskell:

> rev :: (List t) => t a -> t a
> rev = foldl nil cons

</p></div>

<div class="proof"><p>
Recall that $\rev = \foldr{\nil}{\snoc}$ by definition. Note that $\foldr{\nil}{\cons} = \id$ by the universal property of $\foldr{\ast}{\ast}$. So we have
$$\begin{eqnarray*}
 &   & \foldl{\nil}{\cons} \\
 & = & \foldr{\nil}{\cons} \circ \rev \\
 & = & \id \circ \rev \\
 & = & \rev
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

A useful question to ask is this: under what circumstances can a function be defined using either a right fold or a left fold? The next result provides a sufficient condition.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets, and suppose $\varphi : A \times B \rightarrow B$ has the property that $$\varphi(a,\varphi(b,e)) = \varphi(b,\varphi(a,e))$$ for all $a,b \in A$ and $e \in B$. Then we have the following.

1. $\foldr{e}{\varphi}(\snoc(a,x)) = \foldr{e}{\varphi}(\cons(a,x))$.
2. $\foldr{e}{\varphi}(\rev(x)) = \foldr{e}{\varphi}(x)$.
3. In particular, $\foldr{e}{\varphi} = \foldl{e}{\varphi}$.
</p></div>

<div class="proof"><p>
1. We consider two cases. If $x = \nil$, we have $$\foldr{e}{\varphi}(\snoc(a,\nil)) = \foldr{e}{\varphi}(\cons(a,\nil))$$ as claimed. Suppose instead that $x = \cons(b,w)$; we now proceed by list induction on $w$. For the base case $w = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\snoc(a,\cons(b,\nil))) \\
 & = & \foldr{\varphi(a,e)}{\varphi}(\cons(b,\nil)) \\
 & = & \varphi(b,\foldr{\varphi(a,e)}{\varphi}(\nil)) \\
 & = & \varphi(b,\varphi(a,e)) \\
 & = & \varphi(a,\varphi(b,e)) \\
 & = & \varphi(a,\varphi(b,\foldr{e}{\varphi}(\nil))) \\
 & = & \varphi(a,\foldr{e}{\varphi}(\cons(b,\nil))) \\
 & = & \foldr{e}{\varphi}(\cons(a,\cons(b,\nil)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $w$ and let $c \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\snoc(a,\cons(b,\cons(c,w)))) \\
 & = & \foldr{\varphi(a,e)}{\varphi}(\cons(b,\cons(c,w))) \\
 & = & \varphi(b,\foldr{\varphi(a,e)}{\varphi}(\cons(c,w))) \\
 & = & \varphi(b,\varphi(c,\foldr{\varphi(a,e)}{\varphi}(w))) \\
 & = & \varphi(b,\varphi(c,\foldr{e}{\varphi}(\snoc(a,w)))) \\
 & = & \varphi(b,\varphi(c,\foldr{e}{\varphi}(\cons(a,w)))) \\
 & = & \varphi(b,\varphi(c,\varphi(a,\foldr{e}{\varphi}(w)))) \\
 & = & \varphi(b,\varphi(a,\varphi(c,\foldr{e}{\varphi}(w)))) \\
 & = & \varphi(a,\varphi(b,\varphi(c,\foldr{e}{\varphi}(w)))) \\
 & = & \foldr{e}{\varphi}(\cons(a,\cons(b,\cons(c,w))))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\rev(x)) \\
 & = & \foldr{e}{\varphi}(\rev(\nil)) \\
 & = & \foldr{e}{\varphi}(\nil) \\
 & = & \foldr{e}{\varphi}(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \foldr{e}{\varphi}(\rev(\cons(a,x))) \\
 & = & \foldr{e}{\varphi}(\snoc(a,\rev(x))) \\
 & = & \foldr{e}{\varphi}(\cons(a,\rev(x))) \\
 & = & \varphi(a,\foldr{e}{\varphi}(\rev(x))) \\
 & = & \varphi(a,\foldr{e}{\varphi}(x)) \\
 & = & \foldr{e}{\varphi}(\cons(a,x))
\end{eqnarray*}$$
as needed.
3. This is a restatement of (2).
</p></div>
</div>


Testing
-------

Here are our property tests.

> -- snoc(a,cons(b,x)) == cons(b,snoc(a,x))
> _test_snoc_cons_commute :: (List t, Equal a)
>   => t a -> a -> a -> ListOf t a -> Bool
> _test_snoc_cons_commute _ a b x =
>   (snoc a (cons b x)) ==== (cons b (snoc a x))
> 
> 
> -- rev(cons(a,nil)) == cons(a,nil)
> _test_rev_single :: (List t, Equal a)
>   => t a -> a -> Bool
> _test_rev_single z a =
>   let
>     nil' = nil `withTypeOf` (ListOf z)
>   in
>     (rev (cons a nil')) ==== (cons a nil')
> 
> 
> -- rev(cons(a,cons(b,nil))) == cons(b,cons(a,nil))
> _test_rev_double :: (List t, Equal a)
>   => t a -> a -> a -> Bool
> _test_rev_double z a b =
>   let
>     nil' = nil `withTypeOf` (ListOf z)
>   in
>     (rev (cons a (cons b nil'))) ==== (cons b (cons a nil'))
> 
> 
> -- rev(snoc(a,x)) == cons(a,rev(x))
> _test_rev_snoc :: (List t, Equal a)
>   => t a -> a -> a -> ListOf t a -> Bool
> _test_rev_snoc _ a b x =
>   (rev (snoc a x)) ==== (cons a (rev x))
> 
> 
> -- rev(rev(x)) == x
> _test_rev_involution :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_rev_involution _ x =
>   (rev (rev x)) ==== x
> 
> 
> -- rev(x) == rev'(x)
> _test_rev_alt :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_rev_alt _ x =
>   (rev x) ==== (rev' x)

And the suite:

> -- run all tests for snoc and rev
> _test_rev ::
>   ( Equal a, Show a, Arbitrary a
>   , List t
>   ) => t a -> Int -> Int -> IO ()
> _test_rev t maxSize numCases = do
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_snoc_cons_commute t)
>   runTest args (_test_rev_single t)
>   runTest args (_test_rev_double t)
>   runTest args (_test_rev_snoc t)
>   runTest args (_test_rev_involution t)
>   runTest args (_test_rev_alt t)

And the main function:

> main_rev :: IO ()
> main_rev = do
>   _test_rev (nil :: ConsList Bool) 20 100
>   _test_rev (nil :: ConsList Unary) 20 100
