---
title: Cat
author: nbloomf
date: 2017-04-25
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
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


Testing
-------

Here are our property tests for $\cat$.

> -- cat(nil,x) == x and cat(x,nil) == x
> _test_cat_nil :: (ListOf t, Eq (t a)) => t a -> t a -> Bool
> _test_cat_nil _ a = and
>   [ a == cat nil a
>   , a == cat a nil
>   ]

And the suite:

> -- run all tests for cat
> _test_cat :: (ListOf t, Arbitrary a, Show a, Arbitrary (t a), Show (t a), Eq (t a))
>   => t a -> Int -> Int -> IO ()
> _test_cat t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_cat_nil t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_cat :: IO ()
> main_cat = _test_cat (nil :: List Bool) 20 100
