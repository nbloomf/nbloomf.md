---
title: TakeBut and DropBut
author: nbloomf
date: 2017-12-15
tags: arithmetic-made-difficult, literate-haskell
slug: takebut-dropbut
---

> module TakeButAndDropBut
>   ( takeBut, dropBut, _test_takebut_dropbut, main_takebut_dropbut
>   ) where
> 
> import Prelude ()
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> import MaxAndMin
> import Lists
> import Snoc
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
> import Sublist
> import Select
> import Unique
> import Delete
> import Dedupe
> import TakeAndDrop

Today we'll define two functions, $\takeBut$ and $\dropBut$, analogous to $\take$ and $\drop$, but acting from the end of the list rather than from the beginning. We'd like $\takeBut$ to have a signature like $$\takeBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$$ such that $\takeBut(k)(x)$ is obtained by lopping off the last $k$ items in $x$, and similarly $\dropBut(k)(x)$ lops off all but the last $k$ items. The simplest way to do this is with $\take$, $\drop$, and $\rev$; explicit recursion is not required.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\takeBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$ by $$\takeBut(k)(x) = \rev(\drop(k)(\rev(x)))$$ and define $\dropBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$ by $$\dropBut(k)(x) = \rev(\take(k)(\rev(x))).$$

In Haskell:

> takeBut :: (Natural n, List t) => n -> t a -> t a
> takeBut k x = rev (drop k (rev x))
> 
> dropBut :: (Natural n, List t) => n -> t a -> t a
> dropBut k x = rev (take k (rev x))

</p></div>
</div>

The defining equations for $\drop$ have $\takeBut$ equivalents.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x \in \lists{A}$, $a \in A$, and $k \in \nats$. Then we have the following.

1. $\takeBut(\zero)(x) = x$.
2. $\takeBut(\next(k))(\nil) = \nil$.
3. $\takeBut(\next(k))(\snoc(a,x)) = \takeBut(k)(x)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \takeBut(\zero)(x) \\
 & = & \rev(\drop(\zero)(\rev(x))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \takeBut(\next(k))(\nil) \\
 & = & \rev(\drop(\next(k))(\rev(\nil))) \\
 & = & \rev(\drop(\next(k))(\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \takeBut(\next(k))(\snoc(a,x)) \\
 & = & \rev(\drop(\next(k))(\rev(\snoc(a,x)))) \\
 & = & \rev(\drop(\next(k))(\cons(a,\rev(x)))) \\
 & = & \rev(\drop(k)(\rev(x))) \\
 & = & \takeBut(k,x)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_takeBut_zero :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_takeBut_zero _ n =
>   testName "takeBut(zero)(x) == x" $
>   \x -> eq (takeBut (zero `withTypeOf` n) x) x
> 
> 
> _test_takeBut_next_nil :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> Bool)
> _test_takeBut_next_nil t _ =
>   testName "takeBut(next(n))(nil) == nil" $
>   \n -> eq (takeBut (next n) nil) (nil `withTypeOf` t)
> 
> 
> _test_takeBut_next_snoc :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_takeBut_next_snoc _ _ =
>   testName "takeBut(next(n))(snoc(a,x)) == takeBut(k)(x)" $
>   \n a x -> eq
>     (takeBut (next n) (snoc a x))
>     (takeBut n x)

</p></div>
</div>

$\takeBut$ is a prefix.

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

<div class="test"><p>

> _test_takeBut_prefix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_prefix _ m =
>   testName "prefix(takeBut(k,x),x) == true" $
>   \k x -> eq (prefix (takeBut k x) x) True

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

<div class="test"><p>

> _test_takeBut_sublist :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_sublist _ m =
>   testName "sublist(takeBut(k,x),x) == true" $
>   \k x -> eq (sublist (takeBut k x) x) True

</p></div>
</div>

Now for $\dropBut$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have the following.

1. $\dropBut(\zero,x) = \nil$.
2. $\dropBut(\next(k),\nil) = \nil$.
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

<div class="test"><p>

> _test_dropBut_zero :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_dropBut_zero _ n =
>   testName "dropBut(zero)(x) == nil" $
>   \x -> eq (dropBut (zero `withTypeOf` n) x) nil
> 
> 
> _test_dropBut_next_nil :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> Bool)
> _test_dropBut_next_nil t _ =
>   testName "dropBut(next(n))(nil) == nil" $
>   \n -> eq (dropBut (next n) nil) (nil `withTypeOf` t)
> 
> 
> _test_dropBut_next_snoc :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_dropBut_next_snoc _ _ =
>   testName "dropBut(next(n))(snoc(a,x)) == snoc(a,dropBut(k)(x))" $
>   \n a x -> eq
>     (dropBut (next n) (snoc a x))
>     (snoc a (dropBut n x))

</p></div>
</div>

$\dropBut$ is a $\suffix$.

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

<div class="test"><p>

> _test_dropBut_suffix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_dropBut_suffix _ _ =
>   testName "suffix(dropBut(k,x),x) == true" $
>   \k x -> eq (suffix (dropBut k x) x) True

</p></div>
</div>

$\dropBut$ is idempotent.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\dropBut(k,\dropBut(k,x)) = \dropBut(k,x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \dropBut(k,\dropBut(k,x)) \\
 & = & \dropBut(k,\rev(\take(k,\rev(x)))) \\
 & = & \rev(\take(k,\rev(\rev(\take(k,\rev(x)))))) \\
 & = & \rev(\take(k,\take(k,\rev(x)))) \\
 & = & \rev(\take(k,\rev(x))) \\
 & = & \dropBut(k,x)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_dropBut_idempotent :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_dropBut_idempotent _ _ =
>   testName "dropBut(k,dropBut(k,x)) == dropBut(k,x)" $
>   \k x -> eq (dropBut k (dropBut k x)) (dropBut k x)

</p></div>
</div>

Like $\take$ and $\drop$, $\takeBut$ and $\dropBut$ give a kind of $\cat$-factorization.

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

<div class="test"><p>

> _test_takeBut_dropBut_cat :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_dropBut_cat _ _ =
>   testName "cat(takeBut(k,x),dropBut(k,x)) == x" $
>   \k x -> eq (cat (takeBut k x) (dropBut k x)) x

</p></div>
</div>


Testing
-------

Suite:

> _test_takebut_dropbut ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
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
>   runTest args (_test_takeBut_zero t k)
>   runTest args (_test_takeBut_next_nil t k)
>   runTest args (_test_takeBut_next_snoc t k)
>   runTest args (_test_takeBut_prefix t k)
>   runTest args (_test_takeBut_sublist t k)
> 
>   runTest args (_test_dropBut_zero t k)
>   runTest args (_test_dropBut_next_nil t k)
>   runTest args (_test_dropBut_next_snoc t k)
>   runTest args (_test_dropBut_suffix t k)
>   runTest args (_test_dropBut_idempotent t k)
> 
>   runTest args (_test_takeBut_dropBut_cat t k)

Main:

> main_takebut_dropbut :: IO ()
> main_takebut_dropbut = do
>   _test_takebut_dropbut (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_takebut_dropbut (nil :: ConsList Unary) (zero :: Unary) 20 100
