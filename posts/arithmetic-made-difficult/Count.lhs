---
title: Count
author: nbloomf
date: 2017-05-21
tags: arithmetic-made-difficult, literate-haskell
slug: count
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Count
>   ( count, addcount, _test_count, main_count
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Plus
> import Lists
> import HeadAndTail
> import LeftFold
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import PrefixAndSuffix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt

Today we'll define $\count$, which takes an $A$ and a $\lists{A}$ and returns the number of items in the $\lists{A}$ that are identical to the $A$. As usual we'll define this as a fold. Note that -- unlike some of the other list functions  we've seen -- in principle, $\count$ shouldn't care so much what *order* the items in its input come in. Moreover, note that $\count$ necessarily must examine every item in its input if it's going to return the correct answer. When this happens -- we don't care about order but have to look at every item -- the *left fold* operator can be used instead of the right fold, with the advantage that left fold is more space efficient.

When dealing with left folds, it is often handier to parameterize on the base case, so that's what we'll do.

<div class="result">
<div class="defn"><p>
Let $A$ be a set with $a \in A$, and define $\varphi : \nats \times A \rightarrow \nats$ by $$\varphi(k,b) = \bif{\beq(a,b)}{\next(k)}{k}.$$ Now we define $\addcount(a) : \nats \times \lists{A} \rightarrow \nats$ by $$\addcount(a)(n,x) = \foldl{\varphi}(n)(x).$$

In Haskell:

> addcount:: (List t, Equal a, Natural n) => a -> n -> t a -> n
> addcount a = foldl phi
>   where
>     phi k b = if eq a b then next k else k

</p></div>
</div>

Since $\addcount$ is defined as a left fold, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set with $a \in A$. Then $\addcount$ is the unique map $f : \nats \times \lists{A} \rightarrow \nats$ satisfying the following system of equations for all $k \in \nats$, $b \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(k,\nil) = k \\
 f(k,\cons(b,x)) = f(\bif{\beq(a,b)}{\next(k)}{k},x)
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_addcount_nil :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> Bool)
> _test_addcount_nil t _ =
>   testName "addcount(a)(k,nil) == k" $
>   \a k -> eq (addcount a k (nil `withTypeOf` t)) k
> 
> 
> _test_addcount_cons :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> a -> t a -> Bool)
> _test_addcount_cons _ _ =
>   testName "addcount(a)(k,cons(b,x)) == addcount(a)(if(eq(a,b),next(k),k),x)" $
>   \a k b x -> eq (addcount a k (cons b x)) (addcount a (if eq a b then next k else k) x)

</p></div>
</div>

$\addcount$ interacts with $\next$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\addcount(a)(\next(k),x) = \next(\addcount(a)(k,x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \addcount(a)(\next(k),\nil) \\
 & = & \next(k) \\
 & = & \next(\addcount(a)(k,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \addcount(a)(\next(k),\cons(b,x)) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(\next(k))}{\next(k)},x) \\
 & = & \next(\addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},x)) \\
 & = & \next(\addcount(a)(k,\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_addcount_next :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> t a -> Bool)
> _test_addcount_next _ _ =
>   testName "addcount(a)(next(k),x) == next(addcount(a)(k,x))" $
>   \a k x -> eq (addcount a (next k) x) (next (addcount a k x))

</p></div>
</div>

Now $\addcount$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$. For all $b \in A$ and $x \in \lists{A}$, we have $$\addcount(a)(k,\snoc(b,x)) = \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\snoc(b,\nil)) \\
 & = & \addcount(a)(k,\cons(b,\nil)) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $b$ and $k$ for some $x$, and let $c \in A$. Now
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\snoc(b,\cons(c,x))) \\
 & = & \addcount(a)(k,\cons(c,\snoc(b,x))) \\
 & = & \addcount(a)(\bif{\beq(a,c)}{\next(k)}{k},\snoc(b,x)) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(\bif{\beq(a,c)}{\next(k)}{k})}{\bif{\beq(a,c)}{\next(k)}{k}},x) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\bif{\beq(a,c)}{\next(\next(k))}{\next(k)}}{\bif{\beq(a,c)}{\next(k)}{k}},x) \\
 & = & \addcount(a)(\bif{\beq(a,c)}{\bif{\beq(a,b)}{\next(\next(k))}{\next(k)}}{\bif{\beq(a,b)}{\next(k)}{k}},x) \\
 & = & \addcount(a)(\bif{\beq(a,c)}{\next(\bif{\beq(a,b)}{\next(k)}{k})}{\bif{\beq(a,b)}{\next(k)}{k}},x) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},\cons(c,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_addcount_snoc :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> a -> t a -> Bool)
> _test_addcount_snoc _ _ =
>   testName "addcount(a)(k,snoc(b,x)) == addcount(a)(if(eq(a,b),next(k),k),x)" $
>   \a k b x -> eq (addcount a k (snoc b x)) (addcount a (if eq a b then next k else k) x)

</p></div>
</div>

$\addcount$ interacts with $\rev$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\addcount(a)(k,\rev(x)) = \addcount(a)(k,x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\rev(\nil)) \\
 & = & \addcount(a)(k,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\rev(\cons(b,x))) \\
 & = & \addcount(a)(k,\snoc(b,\rev(x))) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},\rev(x)) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},x) \\
 & = & \addcount(a)(k,\cons(b,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_addcount_rev :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> t a -> Bool)
> _test_addcount_rev _ _ =
>   testName "addcount(a)(k,rev(x)) == addcount(a)(k,x)" $
>   \a k x -> eq (addcount a k (rev x)) (addcount a k x)

</p></div>
</div>

We can also characterize $\addcount$ as a right fold.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$, and define $\psi : A \times \nats \rightarrow \nats$ by $$\psi(b,k) = \bif{\beq(a,b)}{\next(k)}{k}.$$ Then we have $$\addcount(a)(k,x) = \foldr{k}{\psi}(x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\nil) \\
 & = & k \\
 & = & \foldr{k}{\psi}(\nil)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \addcount(a)(k,\cons(b,x)) \\
 & = & \addcount(a)(\bif{\beq(a,b)}{\next(k)}{k},x) \\
 & = & \bif{\beq(a,b)}{\addcount(a)(\next(k),x)}{\addcount(a)(k,x)} \\
 & = & \bif{\beq(a,b)}{\next(\addcount(a)(k,x))}{\addcount(a)(k,x)} \\
 & = & \psi(b,\addcount(a)(k,x)).
\end{eqnarray*}$$
By the universal property of right fold, the equality holds for all $x$.
</p></div>

<div class="test"><p>

> _test_addcount_foldr :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> t a -> Bool)
> _test_addcount_foldr _ _ =
>   testName "addcount(a)(k,x) == foldr(k,psi)(x)" $
>   \a k x ->
>     let psi b k = if eq a b then next k else k in
>     eq (addcount a k x) (foldr k psi x)

</p></div>
</div>

So we can evaluate $\addcount$ as a left fold, but reason about $\count$ as a right fold. Since $\addcount(a)$ is also a right fold, it can be characterized as the unique solution to a (different) system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set with $a \in A$. Now $\addcount(a)$ is the unique map $f : \nats \times \lists{A} \rightarrow \nats$ satisfying the following equations for all $b \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(k,\nil) = k \\
 f(k,\cons(b,x)) = \bif{\beq(a,b)}{\next(f(k,x))}{f(k,x)}
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_addcount_foldr_cons :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> n -> a -> t a -> Bool)
> _test_addcount_foldr_cons _ _ =
>   testName "addcount(a)(k,cons(b,x)) == if(eq(a,b),next(addcount(a)(k,x)),addcount(a)(k,x))" $
>   \a k b x -> eq
>     (addcount a k (cons b x))
>     (if eq a b then next (addcount a k x) else addcount a k x)

</p></div>
</div>

We define $\count$ in terms of $\addcount$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set with $a \in A$. We define $\count : A \rightarrow \nats^{\lists{A}}$ by $$\count(a)(x) = \addcount(a)(\zero,x).$$

In Haskell:

> count :: (List t, Equal a, Natural n) => a -> t a -> n
> count a = addcount a zero

</p></div>
</div>

Since $\count$ is defined in terms of $\addcount$, it is also the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set with $a \in A$. Then $\count(a)$ is the unique map $f : \lists{A} \rightarrow \nats$ which satisfies the following system of equations for all $b \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \zero \\
 f(\cons(b,x)) = \bif{\beq(a,b)}{\next(f(x))}{f(x)}
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_count_nil :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> Bool)
> _test_count_nil t k =
>   testName "count(a)(nil) == zero" $
>   \a -> eq (count a (nil `withTypeOf` t)) (zero `withTypeOf` k)
> 
> 
> _test_count_cons :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> a -> t a -> Bool)
> _test_count_cons _ k =
>   testName "count(a)(cons(b,x)) == if(eq(a,b),next(count(a)(x)),count(a)(x))" $
>   \a b x -> eq
>     ((count a (cons b x)) `withTypeOf` k)
>     (if eq a b then next (count a x) else count a x)

</p></div>
</div>

A special case.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $a,b \in A$. Then $$\count(a,\cons(b,\nil)) = \bif{\beq(a,b)}{\next(\zero)}{\zero}.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,\nil)) \\
 & = & \foldl{\zero}{\varphi(a)}(\cons(b,\nil)) \\
 & = & \foldl{\varphi(a)(b,\zero)}{\varphi(a)}(\nil) \\
 & = & \varphi(a)(b,\zero) \\
 & = & \bif{\beq(a,b)}{\next(\zero)}{\zero}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_count_one :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> a -> Bool)
> _test_count_one t k =
>   testName "count(a,cons(b,nil)) == if(eq(a,b),next(zero),zero)" $
>   \a b -> eq
>     (count a (cons b (nil `withTypeOf` t)))
>     (if eq a b then (next zero `withTypeOf` k) else zero)

</p></div>
</div>

$\count$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$. For all $b \in A$ and $x \in \lists{A}$, we have $$\count(a)(\snoc(b,x)) = \bif{\beq(a,b)}{\next(\count(a)(x))}{\count(a)(x)}.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \count(a)(\snoc(b,x)) \\
 & = & \addcount(a)(\zero,\snoc(b,x)) \\
 & = & \bif{\beq(a,b)}{\next(\addcount(a)(\zero,x))}{\addcount(a)(\zero,x)} \\
 & = & \bif{\beq(a,b)}{\next(\count(a)(x))}{\count(a)(x)}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_count_snoc :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> a -> t a -> Bool)
> _test_count_snoc _ k =
>   testName "count(a)(snoc(b,x)) == count(a)(if(eq(a,b),next(k),k),x)" $
>   \a b x -> eq
>     ((count a (snoc b x)) `withTypeOf` k)
>     (if eq a b then next (count a x) else count a x)

</p></div>
</div>

$\count$ interacts with $\rev$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$. For all $x \in \lists{A}$ we have $$\count(a)(\rev(x)) = \count(a)(x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \count(a)(\rev(x)) \\
 & = & \addcount(a)(\zero,\rev(x)) \\
 & = & \addcount(a)(\zero,\x) \\
 & = & \count(a)(x)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_count_rev :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_count_rev _ k =
>   testName "count(a)(rev(x)) == count(a)(x)" $
>   \a x -> eq (count a (rev x)) ((count a x) `withTypeOf` k)

</p></div>
</div>

$\count$ interacts with $\cat$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have $$\count(a,\cat(x,y)) = \nplus(\count(a,x),\count(a,y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(x,y)) \\
 & = & \count(a,\cat(\nil,y)) \\
 & = & \count(a,y) \\
 & = & \nplus(\zero,\count(a,y)) \\
 & = & \nplus(\count(a,\nil),\count(a,y)) \\
 & = & \nplus(\count(a,x),\count(a,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ and $a$ for some $x$, and let $b \in A$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(\cons(b,x),y)) \\
 & = & \count(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,\cat(x,y)))}{\count(a,\cat(x,y))} \\
 & = & \next(\count(a,\cat(x,y))) \\
 & = & \next(\nplus(\count(a,x),\count(a,y))) \\
 & = & \nplus(\next(\count(a,x)),\count(a,y)) \\
 & = & \nplus(\bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)},\count(a,y)) \\
 & = & \nplus(\count(a,\cons(b,x)),\count(a,y))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(\cons(b,x),y)) \\
 & = & \count(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,\cat(x,y)))}{\count(a,\cat(x,y))} \\
 & = & \count(a,\cat(x,y)) \\
 & = & \nplus(\count(a,x),\count(a,y)) \\
 & = & \nplus(\bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)},\count(a,y)) \\
 & = & \nplus(\count(a,\cons(b,x)),\count(a,y))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_count_cat :: (List t, Equal a, Natural n, Equal n)
>    => t a -> n -> Test (a -> t a -> t a -> Bool)
> _test_count_cat _ k =
>   testName "count(a,cat(x,y)) == plus(count(a,x),count(a,y))" $
>   \a x y -> eq
>     ((count a (cat x y)) `withTypeOf` k)
>     (plus (count a x) (count a y))

</p></div>
</div>

$\count$ is a $\length$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. We have $$\count(a,x) = \length(\filter(\beq(a,-),x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,x) \\
 & = & \count(a,\nil) \\
 & = & \foldr{\zero}{\varphi(a)}(\nil) \\
 & = & \zero \\
 & = & \length(\nil) \\
 & = & \length(\filter(\beq(a,-),\nil)) \\
 & = & \length(\filter(\beq(a,-),x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,\cons(a,x)) \\
 & = & \bif{\beq(a,a)}{\next(\count(a,x))}{\count(a,x)} \\
 & = & \next(\count(a,x)) \\
 & = & \next(\length(\filter(\beq(a,-),x))) \\
 & = & \length(\cons(a,\filter(\beq(a,-),x))) \\
 & = & \length(\filter(\beq(a,-),\cons(a,x)))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)} \\
 & = & \count(a,x) \\
 & = & \length(\filter(\beq(a,-),x)) \\
 & = & \length(\filter(\beq(a,-),\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_count_length :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_count_length t k =
>   testName "count(a,x) == length(filter(eq(a,-),x))" $
>   \a x -> eq
>     (count a x `withTypeOf` k)
>     (length (filter (eq a) x))

</p></div>
</div>

$\count$ interacts with $\map(f)$ when $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets and $f : A \rightarrow B$ an injective map. Then $$\count(a,x) = \count(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,x) \\
 & = & \count(a,\nil) \\
 & = & \count(a,\map(f)(\nil)) \\
 & = & \count(a,\map(f)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $b \in A$. We consider two possibilities. If $a = b$, then $f(a) = f(b)$, and we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,\cons(a,x)) \\
 & = & \next(\count(a,x)) \\
 & = & \next(\count(f(a),\map(f)(x))) \\
 & = & \count(f(a),\cons(f(a),\map(f)(x))) \\
 & = & \count(f(a),\map(f)(\cons(a,x))) \\
 & = & \count(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed. If $a \neq b$, then we have $f(a) \neq f(b)$ (since $f$ is injective), so that
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,x) \\
 & = & \count(f(a),\map(f)(x)) \\
 & = & \count(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \count(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Suite:

> _test_count ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a))
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_count t n maxSize numCases = do
>   testLabel2 "count" t n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_addcount_nil t n)
>   runTest args (_test_addcount_cons t n)
>   runTest args (_test_addcount_next t n)
>   runTest args (_test_addcount_snoc t n)
>   runTest args (_test_addcount_rev t n)
>   runTest args (_test_addcount_foldr t n)
>   runTest args (_test_addcount_foldr_cons t n)
> 
>   runTest args (_test_count_nil t n)
>   runTest args (_test_count_cons t n)
>   runTest args (_test_count_one t n)
>   runTest args (_test_count_snoc t n)
>   runTest args (_test_count_rev t n)
>   runTest args (_test_count_cat t n)
>   runTest args (_test_count_length t n)

Main:

> main_count :: IO ()
> main_count = do
>   _test_count (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_count (nil :: ConsList Unary) (zero :: Unary) 20 100
