---
title: Cat
author: nbloomf
date: 2017-04-25
tags: arithmetic-made-difficult, literate-haskell
slug: cat
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Cat
>   ( cat, _test_cat, main_cat
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import Snoc
> import Reverse

In this post we'll consider the function that takes two lists and appends one to the "end" of the other. This function is known as $\cat$, which is short for *catenate* -- a jargony word that means *to connect in a series*.

:::::: definition ::
We define a map $\cat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\cat(x,y) = \foldr{y}{\cons}(x).$$

In Haskell:

> cat :: (List t) => t a -> t a -> t a
> cat x y = foldr y cons x

::::::::::::::::::::

Because $\cat$ is defined in terms of fold, it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\cat$ is the unique mapping $f : \lists{A} \times \lists{A} \rightarrow \lists{A}$ with the property that for all $a \in A$ and $x,y \in \lists{A}$ we have
$$\left\{\begin{array}{l}
 f(\nil,y) = y \\
 f(\cons(a,x),y) = \cons(a,f(x,y)).
\end{array}\right.$$

::: test :::::::::::

> _test_cat_nil_left :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_cat_nil_left _ =
>   testName "cat(nil,x) == x" $
>   \a -> eq (cat nil a) a
> 
> 
> _test_cat_cons_left :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_cat_cons_left _ =
>   testName "cat(cons(a,x),y) == cons(a,cat(x,y))" $
>   \a x y -> eq (cat (cons a x) y) (cons a (cat x y))

::::::::::::::::::::
::::::::::::::::::::

Note that $\cat$ works a lot like $\snoc$; it marches down the list $x$ until it reaches the end, and then sticks $y$ there. In some ways, $\cat$ is like $\nplus$ for lists, and $\nil$ is the $\zero$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $\cat(x,\nil) = x$.

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \cat(x,\nil) \\
 & = & \foldr{\nil}{\cons}(x) \\
 & = & \id(x) \\
 &     \href{@functions@#def-id}
   = & x
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_nil_right :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_cat_nil_right _ =
>   testName "cat(x,nil) == x" $
>   \a -> eq (cat a nil) a

::::::::::::::::::::
::::::::::::::::::::

$\cat$ interacts with $\snoc$:

:::::: theorem :::::
Let $A$ be a set. The following hold for all $a \in A$ and $x,y \in \lists{A}$.

1. $\cat(\snoc(a,x),y) = \cat(x,\cons(a,y))$.
2. $\cat(x,\snoc(a,y)) = \snoc(a,\cat(x,y))$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \cat(x,\cons(a,y)) \\
 & = & \foldr{\cons(a,y)}{\cons}(x) \\
 & = & \foldr{y}{\cons}(\snoc(a,y)) \\
 & = & \cat(x,\snoc(a,y))
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $y$. For the base case $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \snoc(a,\cat(x,\nil)) \\
 & = & \snoc(a,x) \\
 &     \href{@snoc@#def-snoc}
   = & \foldr{\cons(a,\nil)}{\cons}(x) \\
 & = & \cat(x,\cons(a,\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \snoc(a,\cat(x,\cons(b,y))) \\
 & = & \snoc(a,\cat(\snoc(b,x),y)) \\
 & = & \cat(\snoc(b,x),\snoc(a,y)) \\
 & = & \cat(x,\cons(b,\snoc(a,y))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \cat(x,\snoc(a,\cons(b,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_snoc_left :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_cat_snoc_left _ =
>   testName "cat(x,cons(a,y)) == cat(snoc(a,x),y)" $
>   \a x y -> eq (cat x (cons a y)) (cat (snoc a x) y)
> 
> 
> _test_cat_snoc_right :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_cat_snoc_right _ =
>   testName "snoc(a,cat(x,y)) == cat(x,snoc(a,y))" $
>   \a x y -> eq (snoc a (cat x y)) (cat x (snoc a y))

::::::::::::::::::::
::::::::::::::::::::

We can "solve" a simple list equation.

:::::: theorem :::::
We have $\nil = \cat(x,y)$ if and only if $x = y = \nil$.

::: proof ::::::::::
The "only if" direction is clear. To see the "if" direction, suppose we have $x,y \in \lists{A}$ such that $\cat(x,y) = \nil$. If $x = \cons(a,u)$, then
$$\begin{eqnarray*}
 &   & \btrue \\
 &     \href{@head-tail@#thm-isnil-nil}
   = & \isnil(\nil) \\
 & = & \isnil(\cat(x,y)) \\
 & = & \isnil(\cat(\cons(a,u),y)) \\
 & = & \isnil(\cons(a,\cat(u,y))) \\
 &     \href{@head-tail@#thm-isnil-cons}
   = & \bfalse
\end{eqnarray*}$$
which is absurd. Thus $x = \nil$, and we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \isnil(\cat(\nil,y)) \\
 & = & \isnil(y)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_nil_nil :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_cat_nil_nil _ =
>   testName "isNil(cat(x,y)) == and(isNil(x),isNil(y))" $
>   \x y -> eq (isNil (cat x y)) (and (isNil x) (isNil y))

::::::::::::::::::::
::::::::::::::::::::

And $\cat$ is associative.

:::::: theorem :::::
Let $A$ be a set and $x,y,z \in \lists{A}$. Then $$\cat(\cat(x,y),z) = \cat(x,\cat(y,z)).$$

::: proof ::::::::::
We proceed by list induction on $z$. For the base case $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \cat(\cat(x,y),\nil) \\
 & = & \cat(x,y) \\
 & = & \cat(x,\cat(y,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $z \in \lists{A}$, and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \cat(\cat(x,y),\cons(a,z)) \\
 & = & \cat(\snoc(a,\cat(x,y)),z) \\
 & = & \cat(\cat(x,\snoc(a,y)),z) \\
 & = & \cat(x,\cat(\snoc(a,y),z)) \\
 & = & \cat(x,\cat(y,\cons(a,z)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_associative :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_cat_associative _ =
>   testName "cat(cat(x,y),z) == cat(x,cat(y,z))" $
>   \x y z -> eq (cat (cat x y) z) (cat x (cat y z))

::::::::::::::::::::
::::::::::::::::::::

And $\rev$ is antidistributive over $\cat$.

:::::: theorem :::::
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\rev(\cat(x,y)) = \cat(\rev(y),\rev(x)).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \rev(\cat(x,\nil)) \\
 & = & \rev(x) \\
 & = & \cat(\nil,\rev(x)) \\
 & = & \cat(\rev(\nil),\rev(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \rev(\cat(x,\cons(a,y))) \\
 & = & \rev(\cat(\snoc(a,x),y)) \\
 & = & \cat(\rev(y),\rev(\snoc(a,x))) \\
 & = & \cat(\rev(y),\cons(a,\rev(x))) \\
 & = & \cat(\snoc(a,\rev(y)),\rev(x)) \\
 & = & \cat(\rev(\cons(a,y)),\rev(x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_rev :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_cat_rev _ =
>   testName "rev(cat(x,y)) == cat(rev(y),rev(x))" $
>   \x y -> eq (rev (cat x y)) (cat (rev y) (rev x))

::::::::::::::::::::
::::::::::::::::::::

Finally, $\cat$ is cancellative.

:::::: theorem :::::
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have the following.

1. $\cat(z,x) = \cat(z,y)$ if and only if $x = y$.
2. $\cat(x,z) = \cat(y,z)$ if and only if $x = y$.

::: proof ::::::::::
1. The "only if" direction is clear. For the "if" direction we proceed by list induction on $z$. For the base case $z = \nil$, suppose $\cat(z,x) = \cat(z,y)$. Then we have
$$\begin{eqnarray*}
 &   & x \\
 & = & \cat(\nil,x) \\
 & = & \cat(z,x) \\
 & = & \cat(z,y) \\
 & = & \cat(\nil,y) \\
 & = & y
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $z$, and let $a \in A$. Now suppose we have $$\cat(\cons(a,z),x) = \cat(\cons(a,z),y).$$ Then we have $\cons(a,\cat(z,x)) = \cons(a,\cat(z,y)),$$ so that $$\cat(z,x) = \cat(z,y).$$ By the inductive hypothesis, $x = y$ as claimed.
2. The "only if" direction is clear. For the "if" direction, note that
$$\begin{eqnarray*}
 &   & \cat(\rev(z),\rev(x)) \\
 & = & \rev(\cat(x,z)) \\
 & = & \rev(\cat(y,z)) \\
 & = & \cat(\rev(z),\rev(y)).
\end{eqnarray*}$$
By (1), we have $\rev(x) = \rev(y)$, and thus $x = y$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_left_cancellative :: (List t, Equal (t a), Boolean b, Equal b)
>   => t a -> b -> Test (t a -> t a -> t a -> Bool)
> _test_cat_left_cancellative _ p =
>   testName "eq(cat(z,x),cat(z,y)) == eq(x,y)" $
>   \x y z -> eq
>     (eq (cat z x) (cat z y))
>     ((eq x y) `withTypeOf` p)
> 
> 
> _test_cat_right_cancellative :: (List t, Equal (t a), Boolean b, Equal b)
>   => t a -> b -> Test (t a -> t a -> t a -> Bool)
> _test_cat_right_cancellative _ p =
>   testName "eq(cat(x,z),cat(y,z)) == eq(x,y)" $
>   \x y z -> eq
>     (eq (cat x z) (cat y z))
>     ((eq x y) `withTypeOf` p)

::::::::::::::::::::
::::::::::::::::::::

One more.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $x,u,v \in \lists{A}$.

1. If $x = \cat(x,v)$ then $v = \nil$.
2. If $x = \cat(u,x)$ then $u = \nil$.
3. If $x = \cat(u,\cat(x,v))$ then $u = v = \nil$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \cat(x,\nil) \\
 & = & x \\
 & = & \cat(x,v),
\end{eqnarray*}$$
so that $v = \nil$ by cancellation.
2. Note that
$$\begin{eqnarray*}
 &   & \cat(\nil,x) \\
 & = & x \\
 & = & \cat(u,x),
\end{eqnarray*}$$
so that $u = \nil$ by cancellation.
3. We proceed by list induction on $x$. For the base case $x = \nil$, if $x = \cat(u,\cat(x,v))$ we have
$$\begin{eqnarray*}
 &   & \nil \\
 & = & x \\
 & = & \cat(u,\cat(x,v)) \\
 & = & \cat(u,\cat(\nil,v)) \\
 & = & \cat(u,v)
\end{eqnarray*}$$
so that $v = u = \nil$ as needed. For the inductive step, suppose the implication holds for all $u$ and $v$ for some $x$, and let $a \in A$. Suppose further that $\cons(a,x) = \cat(u,\cat(\cons(a,x),v))$ for some $u$ and $v$. We consider two possibilities for $u$. If $u = \cons(b,w)$, we have
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cat(u,\cat(\cons(a,x),v)) \\
 & = & \cat(\cons(b,w),\cat(\cons(a,x),v)) \\
 & = & \cons(b,\cat(w,\cat(\cons(a,x),v))).
\end{eqnarray*}$$
So in fact we have $a = b$, and
$$\begin{eqnarray*}
 &   & x \\
 & = & \cat(w,\cat(\cons(a,x),v)) \\
 & = & \cat(\cat(w,\cons(a,x)),v) \\
 & = & \cat(\cat(\snoc(a,w),x),v) \\
 & = & \cat(\snoc(a,w),\cat(x,v)).
\end{eqnarray*}$$
By the inductive hypothesis, we have $\snoc(a,w) = \nil$, a contradiction. So we must have $u = \nil$. Now
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cat(u,\cat(\cons(a,x),v)) \\
 & = & \cat(\nil,\cat(\cons(a,x),v)) \\
 & = & \cat(\cons(a,x),v)
\end{eqnarray*}$$
so that $v = u = \nil$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_cat_right_identity_unique :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_cat_right_identity_unique _ =
>   testName "if eq(cat(x,v),x) then eq(v,nil)" $
>   \x v -> if eq (cat x v) x then eq v nil else true
> 
> 
> _test_cat_left_identity_unique :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_cat_left_identity_unique _ =
>   testName "if eq(cat(u,x),x) then eq(u,nil)" $
>   \x u -> if eq (cat u x) x then eq u nil else true
> 
> 
> _test_cat_nil_list_nil :: (List t, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_cat_nil_list_nil _ =
>   testName "if eq(cat(u,cat(x,v)),x) then and(eq(u,nil),eq(v,nil))" $
>   \x u v -> if eq (cat u (cat x v)) x
>     then and (eq u nil) (eq v nil)
>     else true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_cat ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName (t a), List t, Equal (t a), Show (t a), Arbitrary (t a)
>   , TypeName b, Boolean b, Equal b
>   ) => t a -> b -> Int -> Int -> IO ()
> _test_cat t p maxSize numCases = do
>   testLabel2 "cat" t p
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_cat_nil_left t)
>   runTest args (_test_cat_cons_left t)
>   runTest args (_test_cat_nil_right t)
>   runTest args (_test_cat_snoc_left t)
>   runTest args (_test_cat_snoc_right t)
>   runTest args (_test_cat_nil_nil t)
>   runTest args (_test_cat_associative t)
>   runTest args (_test_cat_rev t)
>   runTest args (_test_cat_left_cancellative t p)
>   runTest args (_test_cat_right_cancellative t p)
>   runTest args (_test_cat_right_identity_unique t)
>   runTest args (_test_cat_left_identity_unique t)
>   runTest args (_test_cat_nil_list_nil t)

Main:

> main_cat :: IO ()
> main_cat = do
>   _test_cat (nil :: ConsList Bool)  (true :: Bool) 20 100
>   _test_cat (nil :: ConsList Unary) (true :: Bool) 20 100
