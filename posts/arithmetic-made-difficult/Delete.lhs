---
title: Delete
author: nbloomf
date: 2017-05-27
tags: arithmetic-made-difficult, literate-haskell
---

> module Delete
>   ( delete, _test_delete, main_delete
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Select
> import Unique
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll establish a function $\delete$ that removes all copies of a given item from a list. $\delete$ is a special case of $\filter$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\delete : A \times \lists{A} \rightarrow \lists{A}$ by $$\delete(a,x) = \filter(\bnot(\beq(a,-)),x).$$

In Haskell:

> delete :: (List t, Equal a) => a -> t a -> t a
> delete a x = filter (\b -> not (eq a b)) x

</p></div>
</div>

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\delete(a,\nil) = \nil$.
2. $\delete(a,\cons(b,x)) = \bif{\beq(a,b)}{\delete(a,x)}{\cons(b,\delete(a,x))}$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \delete(a,\nil) \\
 & = & \filter(\bnot(\beq(a,-)),\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \delete(a,\cons(b,x)) \\
 & = & \filter(\bnot(\beq(a,-)),\cons(b,x)) \\
 & = & \bif{\bnot(\beq(a,b))}{\cons(b,\filter(\bnot(\beq(a,-)),x))}{\filter(\bnot(\beq(a,-)),x)} \\
 & = & \bif{\bnot(\beq(a,b))}{\cons(b,\delete(a,x))}{\delete(a,x)} \\
 & = & \bif{\beq(a,b)}{\delete(a,x)}{\cons(b,\delete(a,x))}
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\delete$ is idempotent.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$ we have $$\delete(a,\delete(a,x)) = \delete(a,x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \delete(a,\delete(a,x)) \\
 & = & \filter(\bnot(\beq(a,-)),\filter(\bnot(\beq(a,-)),x)) \\
 & = & \filter(\bnot(\beq(a,-)),x) \\
 & = & \delete(a,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\delete$ and $\elt$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then we have $$\beq(x,\delete(a,x)) = \bnot(\elt(a,x)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \beq(x,\delete(a,x)) \\
 & = & \beq(x,\filter(\bnot(\beq(a,-)),x)) \\
 & = & \all(\bnot(\beq(a,-)),x) \\
 & = & \bnot(\any(\beq(a,-),x)) \\
 & = & \bnot(\elt(a,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\delete$ commutes with itself.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $a,b \in A$ and $x \in \lists{A}$. Then $$\delete(a,\delete(b,x)) = \delete(b,\delete(a,x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\nil)) \\
 & = & \delete(a,\nil) \\
 & = & \nil \\
 & = & \delete(b,\nil) \\
 & = & \delete(b,\delete(a,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $c \in A$. We consider four possibilities. If $c = a$ and $c = b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. If $c = a$ and $c \neq b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\cons(c,\delete(b,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. If $c \neq a$ and $c = b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\delete(b,x)) \\
 & = & \delete(b,\delete(a,x)) \\
 & = & \delete(b,\cons(c,\delete(a,x))) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed. Finally, if $c \neq a$ and $c \neq b$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \delete(a,\delete(b,\cons(c,x))) \\
 & = & \delete(a,\cons(c,\delete(b,x))) \\
 & = & \cons(c,\delete(a,\delete(b,x))) \\
 & = & \cons(c,\delete(b,\delete(a,x))) \\
 & = & \delete(b,\cons(c,\delete(a,x))) \\
 & = & \delete(b,\delete(a,\cons(c,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\dedupeL$ and $\dedupeR$:

> _test_delete_elt :: (List t, Equal a)
>   => t a -> Test (a -> ListOf t a -> Bool)
> _test_delete_elt _ =
>   testName "eq(x,delete(a,x)) == not(elt(a,x))" $
>   \a x -> (eq x (delete a x)) ==== not (elt a x)

And the suite:

> -- run all tests for delete
> _test_delete ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_delete t maxSize numCases = do
>   testLabel ("delete: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_delete_elt t)

And ``main``:

> main_delete :: IO ()
> main_delete = do
>   _test_delete (nil :: ConsList Bool)  20 100
>   _test_delete (nil :: ConsList Unary) 20 100
