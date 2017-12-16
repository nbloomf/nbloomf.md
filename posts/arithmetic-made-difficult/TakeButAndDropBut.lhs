---
title: TakeBut and DropBut
author: nbloomf
date: 2017-05-29
tags: arithmetic-made-difficult, literate-haskell
---

> module TakeButAndDropBut
>   ( takeBut, dropBut, _test_takebut_dropbut, main_takebut_dropbut
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> import MaxAndMin
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
> import Delete
> import Dedupe
> import TakeAndDrop
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define two functions, $\takeBut$ and $\dropBut$, analogous to $\take$ and $\drop$, but acting from the end of the list rather than from the beginning. We'd like $\takeBut$ to have a signature like $$\takeBut : \nats \times \lists{A} \rightarrow \lists{A}$$ such that $\takeBut(k,x)$ is obtained by lopping off the last $k$ items in $x$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\takeBut : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\takeBut(k,x) = \rev(\drop(k,\rev(x)))$$ and define $\dropBut : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\dropBut(k,x) = \rev(\take(k,\rev(x))).$$

In Haskell:

> takeBut :: (Natural k, List t) => k -> t a -> t a
> takeBut k x = rev (drop k (rev x))
> 
> dropBut :: (Natural k, List t) => k -> t a -> t a
> dropBut k x = rev (take k (rev x))

</p></div>
</div>

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x \in \lists{A}$, $a \in A$, and $k \in \nats$. Then we have the following.

1. $\takeBut(\zero,x) = x$.
2. $\takeBut(k,\nil) = \nil$.
3. $\takeBut(\next(k),\snoc(a,x)) = \takeBut(k,x)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \takeBut(\zero,x) \\
 & = & \rev(\drop(\zero,\rev(x))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \takeBut(k,\nil) \\
 & = & \rev(\drop(k,\rev(\nil))) \\
 & = & \rev(\drop(k,\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \takeBut(\next(k),\snoc(a,x)) \\
 & = & \rev(\drop(\next(k),\rev(\snoc(a,x)))) \\
 & = & \rev(\drop(\next(k),\cons(a,\rev(x)))) \\
 & = & \rev(\drop(k,\rev(x))) \\
 & = & \takeBut(k,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now $\takeBut$ is a prefix:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\prefix(\takeBut(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \prefix(\takeBut(k,x),x) \\
 & = & \prefix(\rev(\drop(k,\rev(x))),x) \\
 & = & \prefix(\rev(\drop(k,\rev(x))),\rev(\rev(x))) \\
 & = & \suffix(\drop(k,\rev(x)),\rev(x)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

So $\takeBut$ is a sublist:

<div class="result">
<div class="corollary"><p>
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\sublist(\takeBut(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have $$\prefix(\takeBut(k,x),x) = \btrue,$$ so $$\infix(\takeBut(k,x),x) = \btrue,$$ so $$\sublist(\takeBut(k,x),x) = \btrue$$ as claimed.
</p></div>
</div>

Now for $\dropBut$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have the following.

1. $\dropBut(\zero,x) = \nil$.
2. $\dropBut(k,\nil) = \nil$.
3. $\dropBut(\next(k),\snoc(a,x)) = \snoc(a,\dropBut(k,x))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \dropBut(\zero,x) \\
 & = & \rev(\take(\zero,\rev(x))) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \dropBut(k,\nil) \\
 & = & \rev(\take(k,\rev(\nil))) \\
 & = & \rev(\take(k,\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \dropBut(\next(k),\snoc(a,x)) \\
 & = & \rev(\take(\next(k),\rev(\snoc(a,x)))) \\
 & = & \rev(\take(\next(k),\cons(a,\rev(x)))) \\
 & = & \rev(\cons(a,\take(k,\rev(x)))) \\
 & = & \snoc(a,\rev(\take(k,\rev(x)))) \\
 & = & \snoc(a,\dropBut(k,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now $\dropBut$ is a $\suffix$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\suffix(\dropBut(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \suffix(\dropBut(k,x),x) \\
 & = & \suffix(\rev(\take(k,\rev(x))),x) \\
 & = & \suffix(\rev(\take(k,\rev(x))),\rev(\rev(x))) \\
 & = & \prefix(\take(k,\rev(x)),\rev(x)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Finally, $\takeBut$ and $\dropBut$ give a kind of $\cat$-factorization.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$x = \cat(\takeBut(k,x),\dropBut(k,x)).$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \cat(\takeBut(k,x),\dropBut(k,x)) \\
 & = & \cat(\rev(\drop(k,\rev(x))),\rev(\take(k,\rev(x)))) \\
 & = & \rev(\cat(\take(k,\rev(x)),\drop(k,\rev(x)))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\takeBut$:

> _test_takeBut_prefix :: (List t, Equal a, Natural k)
>   => t a -> k -> Test (Nat k -> ListOf t a -> Bool)
> _test_takeBut_prefix _ _ =
>   testName "prefix(takeBut(k,x),x) == true" $
>   \k x -> prefix (takeBut k x) x ==== True

And for $\dropBut$:

> _test_dropBut_suffix :: (List t, Equal a, Natural k)
>   => t a -> k -> Test (Nat k -> ListOf t a -> Bool)
> _test_dropBut_suffix _ _ =
>   testName "suffix(dropBut(k,x),x) == true" $
>   \k x -> suffix (dropBut k x) x ==== True

And for both:

> _test_takeBut_dropBut_cat :: (List t, Equal a, Natural k)
>   => t a -> k -> Test (Nat k -> ListOf t a -> Bool)
> _test_takeBut_dropBut_cat _ _ =
>   testName "cat(takeBut(k,x),dropBut(k,x)) == x" $
>   \k x -> (cat (takeBut k x) (dropBut k x)) ==== x

And the suite:

> -- run all tests for takeBut & dropBut
> _test_takebut_dropbut ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_takebut_dropbut t k maxSize numCases = do
>   testLabel ("takeBut & dropBut: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_takeBut_prefix t k)
> 
>   runTest args (_test_dropBut_suffix t k)
> 
>   runTest args (_test_takeBut_dropBut_cat t k)

And ``main``:

> main_takebut_dropbut :: IO ()
> main_takebut_dropbut = do
>   _test_takebut_dropbut (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_takebut_dropbut (nil :: ConsList Unary) (zero :: Unary) 20 100
