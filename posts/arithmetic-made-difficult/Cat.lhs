---
title: Cat
author: nbloomf
date: 2017-04-25
tags: arithmetic-made-difficult, literate-haskell
---

> module Cat
>   ( cat, _test_cat, main_cat
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import Lists
> import Reverse
> 
> import Prelude (Show, Int, IO)
> import Test.QuickCheck

In this post we'll consider the function that takes two lists and appends one to the "end" of the other. This function is known as $\cat$, which is short for *catenate* -- a jargony word that means *to connect in a series*.

<div class="result">
<div class="defn"><p>
We define a map $\cat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\cat(x,y) = \foldr{y}{\cons}(x).$$

In Haskell:

> cat :: (List t) => t a -> t a -> t a
> cat x y = foldr y cons x

</p></div>
</div>

Note that $\cat$ works a lot like $\snoc$; it marches down the list $x$ until it reaches the end, and then sticks $y$ there. In some ways, $\cat$ is like $\nplus$ for lists, and $\nil$ is the $\zero$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have

1. $\cat(x,\nil) = x$.
2. $\cat(\nil,x) = x$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \cat(x,\nil) \\
 & = & \foldr{\nil}{\cons}(x) \\
 & = & \id(x) \\
 & = & x
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \cat(\nil,x) \\
 & = & \foldr{x}{\cons}(\nil) \\
 & = & x
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\cat$ interacts with $\cons$ and $\snoc$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $a \in A$ and $x,y \in \lists{A}$.

1. $\cat(x,\cons(a,y)) = \cat(\snoc(a,x),y)$.
2. $\cons(a,\cat(x,y)) = \cat(\cons(a,x),y)$.
3. $\snoc(a,\cat(x,y)) = \cat(x,\snoc(a,y))$.
</p></div>

<div class="proof"><p>
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
 &   & \cons(a,\cat(x,\nil)) \\
 & = & \cons(a,x) \\
 & = & \cat(\cons(a,x),\nil)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \cons(a,\cat(x,\cons(b,y))) \\
 & = & \cons(a,\cat(\snoc(b,x),y)) \\
 & = & \cat(\cons(a,\snoc(b,x)),y) \\
 & = & \cat(\snoc(b,\cons(a,x)),y) \\
 & = & \cat(\cons(a,x),\cons(b,y))
\end{eqnarray*}$$
as needed.
3. We proceed by list induction on $y$. For the base case $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \snoc(a,\cat(x,\nil)) \\
 & = & \snoc(a,x) \\
 & = & \foldr{\cons(a,\nil)}{\cons}(x) \\
 & = & \cat(x,\cons(a,\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $y \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \snoc(a,\cat(x,\cons(b,y))) \\
 & = & \snoc(a,\cat(\snoc(b,x),y)) \\
 & = & \cat(\snoc(b,x),\snoc(a,y)) \\
 & = & \cat(x,\cons(b,\snoc(a,y))) \\
 & = & \cat(x,\snoc(a,\cons(b,y)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

As a corollary, we can "solve" a simple list equation.

<div class="result">
<div class="corollary"><p>
If $\nil = \cat(x,y)$, then $x = y = \nil$.
</p></div>
</div>

And $\cat$ is associative.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $x,y,z \in \lists{A}$. Then $$\cat(\cat(x,y),z) = \cat(x,\cat(y,z)).$$
</p></div>

<div class="proof"><p>
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
</p></div>
</div>

And $\rev$ is antidistributive over $\cat$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ we have $$\rev(\cat(x,y)) = \cat(\rev(y),\rev(x)).$$
</p></div>

<div class="proof"><p>
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
</p></div>
</div>

Finally, $\cat$ is cancellative.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y,z \in \lists{A}$ we have the following.

1. If $\cat(z,x) = \cat(z,y)$, then $x = y$.
2. If $\cat(x,z) = \cat(y,z)$, then $x = y$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $z$. For the base case $z = \nil$, suppose $\cat(z,x) = \cat(z,y)$. Then we have
$$\begin{eqnarray*}
 &   & x \\
 & = & \cat(\nil,x) \\
 & = & \cat(z,x) \\
 & = & \cat(z,y) \\
 & = & \cat(\nil,y) \\
 & = & y
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $z$, and let $a \in A$. Now suppose we have $$\cat(\cons(a,z),x) = \cat(\cons(a,z),y).$$ Then we have $\cons(a,\cat(z,x)) = \cons(a,\cat(z,y)),$$ so that $$\cat(z,x) = \cat(z,y).$$ By the inductive hypothesis, $x = y$ as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \cat(\rev(z),\rev(x)) \\
 & = & \rev(\cat(x,z)) \\
 & = & \rev(\cat(y,z)) \\
 & = & \cat(\rev(z),\rev(y)).
\end{eqnarray*}$$
By (1), we have $\rev(x) = \rev(y)$, and thus $x = y$ as claimed.
</p></div>
</div>

One more.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,u,v \in \lists{A}$.

1. If $x = \cat(x,v)$ then $v = \nil$.
2. If $x = \cat(u,x)$ then $u = \nil$.
3. If $x = \cat(u,\cat(x,v))$ then $u = v = \nil$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, if $x = \cat(x,v)$ we have
$$\begin{eqnarray*}
 &   & \nil \\
 & = & x \\
 & = & \cat(x,v) \\
 & = & \cat(\nil,v) \\
 & = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. Suppose further that $\cons(a,x) = \cat(\cons(a,x),v)$. Then $$\cons(a,x) = \cons(a,\cat(x,v)),$$ so that $x = \cat(x,v)$, and by the inductive hypothesis, $v = \nil$ as needed.
2. Suppose $x = \cat(u,x)$. Then
$$\begin{eqnarray*}
 &   & \rev(x) \\
 & = & \rev(\cat(u,x)) \\
 & = & \cat(\rev(x),\rev(u));
\end{eqnarray*}$$
by part (1) we have $\rev(u) = \nil$, so that $$u = \rev(\rev(u)) = \rev(\nil) = \nil$$ as claimed.
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
</p></div>
</div>


Testing
-------

Here are our property tests for $\cat$.

> _test_cat_nil :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> Bool)
> _test_cat_nil _ =
>   testName "cat(nil,x) == x and cat(x,nil) == x" $
>   \a -> (a ==== cat nil a) &&& (a ==== cat a nil)
> 
> 
> _test_cat_cons_snoc :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_cat_cons_snoc _ =
>   testName "cat(x,cons(a,y)) == cat(snoc(a,x),y)" $
>   \a x y -> (cat x (cons a y)) ==== (cat (snoc a x) y)
> 
> 
> _test_cat_cons :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_cat_cons _ =
>   testName "cons(a,cat(x,y)) == cat(cons(a,x),y)" $
>   \a x y -> (cons a (cat x y)) ==== (cat (cons a x) y)
> 
> 
> _test_cat_snoc :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> ListOf t a -> Bool)
> _test_cat_snoc _ =
>   testName "snoc(a,cat(x,y)) == cat(x,snoc(a,y))" $
>   \a x y -> (snoc a (cat x y)) ==== (cat x (snoc a y))
> 
> 
> _test_cat_associative :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> ListOf t a -> Bool)
> _test_cat_associative _ =
>   testName "cat(cat(x,y),z) == cat(x,cat(y,z))" $
>   \x y z -> (cat (cat x y) z) ==== (cat x (cat y z))
> 
> 
> _test_cat_rev :: (List t, Equal a)
>   => t a -> Test (ListOf t a -> ListOf t a -> Bool)
> _test_cat_rev _ =
>   testName "rev(cat(x,y)) == cat(rev(y),rev(x))" $
>   \x y -> (rev (cat x y)) ==== (cat (rev y) (rev x))

And the suite:

> -- run all tests for cat
> _test_cat ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_cat t maxSize numCases = do
>   testLabel ("cat:" ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_cat_nil t)
>   runTest args (_test_cat_cons_snoc t)
>   runTest args (_test_cat_cons t)
>   runTest args (_test_cat_snoc t)
>   runTest args (_test_cat_associative t)
>   runTest args (_test_cat_rev t)

And ``main``:

> main_cat :: IO ()
> main_cat = do
>   _test_cat (nil :: ConsList Bool)  20 100
>   _test_cat (nil :: ConsList Unary) 20 100
