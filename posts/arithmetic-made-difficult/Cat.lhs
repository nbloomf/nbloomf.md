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
> import Prelude hiding (foldr, foldl', foldl)
> 
> import Lists
> import Reverse
> 
> import Test.QuickCheck

In this post we'll consider the function that takes two lists and appends one to the "end" of the other. This function is known as $\cat$, which is short for *catenate* -- a jargony word that means *to connect in a series*.

<div class="result">
<div class="defn"><p>
We define a map $\cat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\cat(x,y) = \foldr{y}{\cons}(x).$$

In Haskell:

> cat :: (ListOf t) => t a -> t a -> t a
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


Testing
-------

Here are our property tests for $\cat$.

> -- cat(nil,x) == x and cat(x,nil) == x
> _test_cat_nil :: (ListOf t, Eq a) => t a -> t a -> Bool
> _test_cat_nil _ a = and
>   [ a `listEq` cat nil a
>   , a `listEq` cat a nil
>   ]
> 
> 
> -- cat(x,cons(a,y)) == cat(snoc(a,x),y)
> _test_cat_cons_snoc :: (ListOf t, Eq a) => t a -> a -> t a -> t a -> Bool
> _test_cat_cons_snoc _ a x y =
>   (cat x (cons a y)) `listEq` (cat (snoc a x) y)
> 
> 
> -- cons(a,cat(x,y)) == cat(cons(a,x),y)
> _test_cat_cons :: (ListOf t, Eq a) => t a -> a -> t a -> t a -> Bool
> _test_cat_cons _ a x y =
>   (cons a (cat x y)) `listEq` (cat (cons a x) y)
> 
> 
> -- snoc(a,cat(x,y)) == cat(x,snoc(a,y))
> _test_cat_snoc :: (ListOf t, Eq a) => t a -> a -> t a -> t a -> Bool
> _test_cat_snoc _ a x y =
>   (snoc a (cat x y)) `listEq` (cat x (snoc a y))
> 
> 
> -- cat(cat(x,y),z) == cat(x,cat(y,z))
> _test_cat_associative :: (ListOf t, Eq a) => t a -> t a -> t a -> t a -> Bool
> _test_cat_associative _ x y z =
>   (cat (cat x y) z) `listEq` (cat x (cat y z))
> 
> 
> -- rev(cat(x,y)) == cat(rev(y),rev(x))
> _test_cat_rev :: (ListOf t, Eq a) => t a -> t a -> t a -> Bool
> _test_cat_rev _ x y =
>   (rev (cat x y)) `listEq` (cat (rev x) (rev y))

And the suite:

> -- run all tests for cat
> _test_cat :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_cat t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_cat_nil t)
>   , quickCheckWith args (_test_cat_cons_snoc t)
>   , quickCheckWith args (_test_cat_cons t)
>   , quickCheckWith args (_test_cat_snoc t)
>   , quickCheckWith args (_test_cat_associative t)
>   , quickCheckWith args (_test_cat_rev t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_cat :: IO ()
> main_cat = _test_cat (nil :: List Bool) 20 100
