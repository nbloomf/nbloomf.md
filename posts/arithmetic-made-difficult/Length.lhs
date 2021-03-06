---
title: Length
author: nbloomf
date: 2017-04-26
tags: arithmetic-made-difficult, literate-haskell
slug: length
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Length
>   ( addlength, length, _test_length, main_length
>   ) where
> 
> import Testing
> import Functions
> import Flip
> import NaturalNumbers
> import Plus
> import Lists
> import LeftFold
> import Snoc
> import Reverse
> import Cat

Today we'll measure the sizes of lists with $\length$. Intuitively this function should "count" the "number" of "items" in a list. Thinking recursively, it is reasonable to want the length of $\nil$ to be zero, and the length of $\cons(a,x)$ to be one more than the length of $x$. $\foldr(\ast)(\ast)$ was made for situations like this. But wait! Remember that $\foldr(\ast)(\ast)$ is not tail recursive, so on large lists it may have problems. But $\foldl(\ast)$ is tail recursive, and is interchangeable with $\foldr(\ast)(\ast)$ as long as whatever we're doing to the list doesn't care what *order* the items come in. And it seems reasonable to say that the length of a list is not dependent on the order of its items. So we'll use $\foldl(\ast)$. Recall from $\rev$ that $\foldl(\ast)$ is easier to reason about if it remains parameterized on the "base case". With that in mind, we start with a helper function $\addlength$.

:::::: definition ::
[]{#def-addlength}
Let $A$ be a set. We define $\addlength : \nats \rightarrow \lists{A} \rightarrow \nats$ by $\addlength = \foldl(\compose(\const)(\next))$.

In Haskell:

> addlength :: (List t, Natural n) => n -> t a -> n
> addlength = foldl (compose const next)

::::::::::::::::::::

Since $\addlength$ is defined as a $\foldl(\ast)$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-addlength-nil}[]{#cor-addlength-cons}
Let $A$ be a set. Then $\addlength$ is the unique map $f : \nats \times \lists{A} \rightarrow \nats$ such that for all $n \in \nats$, $a \in A$, and $x \in \lists{A}$, we have
$$\left\{\begin{array}{l}
 f(n,\nil) = n \\
 f(n,\cons(a,x)) = f(\next(n),x)
\end{array}\right.$$

::: test :::::::::::

> _test_addlength_nil_right
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> Bool)
> _test_addlength_nil_right t _ =
>   testName "addlength(n,nil) == n" $
>   \n ->
>     let nil' = nil `withTypeOf` t in
>     eq (addlength n nil') n
> 
> 
> _test_addlength_cons_right
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_addlength_cons_right _ _ =
>   testName "addlength(n,cons(a,x)) == addlength(next(n),x)" $
>   \n a x ->
>     eq (addlength n (cons a x)) (addlength (next n) x)

::::::::::::::::::::
::::::::::::::::::::

$\addlength$ interacts with $\cons$ and $\snoc$.

:::::: theorem :::::
[]{#thm-addlength-snoc-next}[]{#thm-addlength-cons-next}
Let $A$ be a set. For all $n \in \nats$, $a \in A$, and $x \in \lists{A}$, we have the following.

1. $\addlength(n,\snoc(a,x)) = \next(\addlength(n,x))$.
2. $\addlength(n,\cons(a,x)) = \next(\addlength(n,x))$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \addlength(n,\snoc(a,x)) \\
 &     \href{@length@#def-addlength}
   = & \foldl(\compose(\const)(\next))(n,\snoc(a,x)) \\
 &     \href{@snoc@#thm-snoc-foldl}
   = & \compose(\const)(\next)(\foldl(\compose(\const)(\next))(n,x),a) \\
 &     \href{@functions@#def-compose}
   = & \const(\next(\foldl(\compose(\const)(\next))(n,x)))(a) \\
 &     \href{@functions@#def-const}
   = & \next(\foldl(\compose(\const)(\next))(n,x)) \\
 &     \href{@length@#def-addlength}
   = & \next(\addlength(n,x))
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \addlength(n,\cons(a,\nil)) \\
 &     \href{@length@#cor-addlength-cons}
   = & \addlength(\next(n),\nil) \\
 &     \href{@length@#cor-addlength-nil}
   = & \next(n) \\
 &     \href{@length@#cor-addlength-nil}
   = & \next(\addlength(n,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $n$ for some $x$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \addlength(n,\cons(a,\cons(b,x))) \\
 &     \href{@length@#cor-addlength-cons}
   = & \addlength(\next(n),\cons(b,x)) \\
 &     \hyp{\addlength(k,\cons(b,x)) = \next(\addlength(k,x))}
   = & \next(\addlength(\next(n),x)) \\
 &     \href{@length@#cor-addlength-cons}
   = & \next(\addlength(n,\cons(b,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_addlength_snoc_next
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_addlength_snoc_next _ _ =
>   testName "addlength(n,snoc(a,x)) == next(addlength(n,x))" $
>   \n a x ->
>     eq (addlength n (snoc a x)) (next (addlength n x))
> 
> 
> _test_addlength_cons_next
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_addlength_cons_next _ _ =
>   testName "addlength(n,cons(a,x)) == next(addlength(n,x))" $
>   \n a x ->
>     eq (addlength n (cons a x)) (next (addlength n x))

::::::::::::::::::::
::::::::::::::::::::

$\addlength$ interacts with $\rev$.

:::::: theorem :::::
[]{#thm-addlength-rev}
Let $A$ be a set. For all $n \in \nats$ and $x \in \lists{A}$, we have $$\addlength(n,\rev(x)) = \addlength(n,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \addlength(n,\rev(\nil)) \\
 &     \href{@rev@#cor-rev-nil}
   = & \addlength(n,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $n$ for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \addlength(n,\rev(\cons(a,x))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \addlength(n,\snoc(a,\rev(x))) \\
 &     \href{@length@#thm-addlength-snoc-next}
   = & \next(\addlength(n,\rev(x))) \\
 &     \href{@length@#thm-addlength-rev}
   = & \next(\addlength(n,x)) \\
 &     \href{@length@#thm-addlength-cons-next}
   = & \addlength(n,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_addlength_rev
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_addlength_rev _ _ =
>   testName "addlength(n,rev(x)) == addlength(n,x)" $
>   \n x ->
>     eq (addlength n (rev x)) (addlength n x)

::::::::::::::::::::
::::::::::::::::::::

Now we define $\length$ as follows.

:::::: definition ::
[]{#def-length}
Let $A$ be a set. Define $\length : \lists{A} \rightarrow \nats$ by $$\length(x) = \addlength(\zero,x).$$

In Haskell:

> length :: (List t, Natural n) => t a -> n
> length = addlength zero

::::::::::::::::::::

Although $\length$ is essentially defined as a left fold, it can be characterized as a right fold.

:::::: theorem :::::
[]{#thm-length-foldr}
Let $A$ be a set. Then we have $$\length(x) = \foldr(\zero)(\flip(\compose(\const)(\next)))(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldr(\zero)(\flip(\compose(\const)(\next)))(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & \zero \\
 &     \href{@length@#cor-addlength-nil}
   = & \addlength(\zero,\nil) \\
 &     \href{@length@#def-length}
   = & \length(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr(\zero)(\flip(\compose(\const)(\next)))(\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \flip(\compose(\const)(\next))(a,\foldr(\zero)(\flip(\compose(\const)(\next)))(x)) \\
 &     \hyp{\length = \foldr(\zero)(\flip(\compose(\const)(\next)))}
   = & \flip(\compose(\const)(\next))(a,\length(x)) \\
 &     \href{@flip@#def-flip}
   = & \compose(\const)(\next)(\length(x),a) \\
 &     \href{@functions@#def-compose}
   = & \const(\next(\length(x)))(a) \\
 &     \href{@functions@#def-const}
   = & \next(\length(x)) \\
 &     \href{@length@#def-length}
   = & \next(\addlength(\zero,x)) \\
 &     \href{@length@#thm-addlength-cons-next}
   = & \addlength(\zero,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_length_foldr
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_length_foldr _ k =
>   testName "length(x) == foldr(zero,flip(compose(const)(next)))(x)" $
>   \x -> eq
>     (length x)
>     (foldr
>       (zero `withTypeOf` k)
>       (flip (compose const next)) x)

::::::::::::::::::::
::::::::::::::::::::

Since $\length$ is equivalent to a right fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-length-nil}[]{#cor-length-cons}
Let $A$ be a set. $\length$ is the unique solution $f : \lists{A} \rightarrow \nats$ to the following system of equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \zero \\
 f(\cons(a,x)) = \next(f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_length_nil
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test Bool
> _test_length_nil t k =
>   testName "length(nil) == zero" $
>     eq (length (nil `withTypeOf` t)) (zero `withTypeOf` k)
> 
> 
> _test_length_cons
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_length_cons _ k =
>   testName "length(cons(a,x)) == next(length(x))" $
>   \a x -> eq
>     ((length (cons a x)) `withTypeOf` k)
>     (next (length x))

::::::::::::::::::::
::::::::::::::::::::

Special cases.

:::::: theorem :::::
[]{#thm-length-singleton}[]{#thm-length-doubleton}
For all $a,b \in A$, we have:

1. $\length(\cons(a,\nil)) = \next(\zero)$.
2. $\length(\cons(a,\cons(b,\nil))) = \next(\next(\zero))$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \length(\cons(a,\nil)) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\nil)) \\
 &     \href{@length@#cor-length-nil}
   = & \next(\zero)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \length(\cons(a,\cons(b,\nil))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\cons(b,\nil))) \\
 &     \href{@length@#thm-length-singleton}
   = & \next(\next(\zero))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_length_single
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> Bool)
> _test_length_single t k =
>   testName "length(cons(a,nil)) == next(zero)" $
>   \a -> eq
>     ((next zero) `withTypeOf` k)
>     (length (cons a (nil `withTypeOf` t)))
> 
> 
> _test_length_double
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> a -> Bool)
> _test_length_double t k =
>   testName "length(cons(a,cons(b,nil))) == next(next(zero))" $
>   \a b -> eq
>     ((next (next zero)) `withTypeOf` k)
>     (length (cons a (cons b (nil `withTypeOf` t))))

::::::::::::::::::::
::::::::::::::::::::

$\length$ interacts with $\snoc$.

:::::: theorem :::::
[]{#thm-length-snoc}
For all $a \in A$ and $x \in \lists{A}$, we have $$\length(\snoc(a,x)) = \next(\length(x)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \length(\snoc(a,x)) \\
 &     \href{@length@#def-length}
   = & \addlength(\zero,\snoc(a,x)) \\
 &     \href{@length@#thm-addlength-snoc-next}
   = & \next(\addlength(\zero,x)) \\
 &     \href{@length@#def-length}
   = & \next(\length(x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_length_snoc :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (a -> t a -> Bool)
> _test_length_snoc _ k =
>   testName "length(snoc(a,x)) == next(length(x))" $
>   \a x -> eq
>     ((length (snoc a x)) `withTypeOf` k)
>     (next (length x))

::::::::::::::::::::
::::::::::::::::::::

$\length$ is invariant over $\rev$.

:::::: theorem :::::
[]{#thm-length-rev}
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\rev(x)) = \length(x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \length(\rev(x)) \\
 &     \href{@length@#def-length}
   = & \addlength(\zero,\rev(x)) \\
 &     \href{@length@#thm-addlength-rev}
   = & \addlength(\zero,x) \\
 &     \href{@length@#def-length}
   = & \length(x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_length_rev
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_length_rev _ k =
>   testName "length(rev(x)) == length(x)" $
>   \x -> eq
>     ((length (rev x)) `withTypeOf` k)
>     (length x)

::::::::::::::::::::
::::::::::::::::::::

$\length$ turns $\cat$ into $\nplus$.

:::::: theorem :::::
[]{#thm-length-cat}
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\length(\cat(x,y)) = \nplus(\length(x),\length(y)).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, note that
$$\begin{eqnarray*}
 &   & \length(\cat(x,\nil)) \\
 &     \href{@cat@#thm-cat-nil-right}
   = & \length(x) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & \nplus(\length(x),\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \nplus(\length(x),\length(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \length(\cat(x,\cons(a,y))) \\
 &     \href{@cat@#thm-cat-snoc-left}
   = & \length(\cat(\snoc(a,x),y)) \\
 &     \hyp{\length(\cat(z,y)) = \nplus(\length(z),\length(y))}
   = & \nplus(\length(\snoc(a,x)),\length(y)) \\
 &     \href{@length@#thm-length-snoc}
   = & \nplus(\next(\length(x)),\length(y)) \\
 & = & \nplus(\length(x),\next(\length(y))) \\
 &     \href{@length@#cor-length-cons}
   = & \nplus(\length(x),\length(\cons(a,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_length_cat
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> t a -> Bool)
> _test_length_cat _ k =
>   testName "length(cat(x,y)) == plus(length(x),length(y))" $
>   \x y -> eq
>     ((length (cat x y)) `withTypeOf` k)
>     (plus (length x) (length y))

::::::::::::::::::::
::::::::::::::::::::

And $\length$ detects $\nil$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$. Then $x = \nil$ if and only if $\length(x) = 0$.

::: proof ::::::::::
We've already seen that $\length(\nil) = \zero$. Suppose then that $x = \cons(a,u)$; then
$$\begin{eqnarray*}
 &   & \length(x) \\
 &     \hyp{x = \cons(a,u)}
   = & \length(\cons(a,u)) \\
 & = & \next(\length(u));
\end{eqnarray*}$$
in particular, $\length(x) \neq \zero$.
::::::::::::::::::::

::: test :::::::::::

> _test_length_zero
>   :: (List t, Equal (t a), Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_length_zero _ k =
>   testName "eq(length(x),zero) == eq(x,nil)" $
>   \x -> eq
>     (eq (length x) (zero `withTypeOf` k))
>     (eq x nil)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_length ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t a), List t, Equal (t a), Show (t a), Arbitrary (t a)
>   ) => Int -> Int -> t a -> n -> IO ()
> _test_length size cases t n = do
>   testLabel2 "length" t n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_addlength_nil_right t n)
>   runTest args (_test_addlength_cons_right t n)
>   runTest args (_test_addlength_snoc_next t n)
>   runTest args (_test_addlength_cons_next t n)
>   runTest args (_test_addlength_rev t n)
> 
>   runTest args (_test_length_foldr t n)
>   runTest args (_test_length_nil t n)
>   runTest args (_test_length_cons t n)
>   runTest args (_test_length_single t n)
>   runTest args (_test_length_double t n)
>   runTest args (_test_length_snoc t n)
>   runTest args (_test_length_rev t n)
>   runTest args (_test_length_cat t n)
>   runTest args (_test_length_zero t n)

Main:

> main_length :: IO ()
> main_length = do
>   _test_length 20 100 (nil :: ConsList Bool)  (zero :: Unary)
>   _test_length 20 100 (nil :: ConsList Unary) (zero :: Unary)
