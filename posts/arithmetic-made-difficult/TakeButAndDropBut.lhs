---
title: TakeBut and DropBut
author: nbloomf
date: 2017-12-15
tags: arithmetic-made-difficult, literate-haskell
slug: takebut-dropbut
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module TakeButAndDropBut
>   ( takeBut, dropBut, _test_takebut_dropbut, main_takebut_dropbut
>   ) where
> 
> import Testing
> import Booleans
> import NaturalNumbers
> import Lists
> import Snoc
> import Reverse
> import Cat
> import PrefixAndSuffix
> import Sublist
> import TakeAndDrop

Today we'll define two functions, $\takeBut$ and $\dropBut$, analogous to $\take$ and $\drop$, but acting from the end of the list rather than from the beginning. We'd like $\takeBut$ to have a signature like $$\takeBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$$ such that $\takeBut(k)(x)$ is obtained by lopping off the last $k$ items in $x$, and similarly $\dropBut(k)(x)$ lops off all but the last $k$ items. The simplest way to do this is with $\take$, $\drop$, and $\rev$; explicit recursion is not required.

:::::: definition ::
[]{#def-takebut}[]{#def-dropbut}
Let $A$ be a set. We define $\takeBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$ by $$\takeBut(k)(x) = \rev(\drop(k)(\rev(x)))$$ and define $\dropBut : \nats \rightarrow {\lists{A}}^{\lists{A}}$ by $$\dropBut(k)(x) = \rev(\take(k)(\rev(x))).$$

In Haskell:

> takeBut :: (Natural n, List t) => n -> t a -> t a
> takeBut k x = rev (drop k (rev x))
> 
> dropBut :: (Natural n, List t) => n -> t a -> t a
> dropBut k x = rev (take k (rev x))

::::::::::::::::::::

The defining equations for $\drop$ have $\takeBut$ equivalents.

:::::: theorem :::::
[]{#thm-takebut-zero}[]{#thm-takebut-next-nil}[]{#thm-takebut-next-snoc}
Let $A$ be a set, with $x \in \lists{A}$, $a \in A$, and $k \in \nats$. Then we have the following.

1. $\takeBut(\zero)(x) = x$.
2. $\takeBut(\next(k))(\nil) = \nil$.
3. $\takeBut(\next(k))(\snoc(a,x)) = \takeBut(k)(x)$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \takeBut(\zero)(x) \\
 &     \href{@takebut-dropbut@#def-takebut}
   = & \rev(\drop(\zero)(\rev(x))) \\
 &     \href{@take-drop@#cor-drop-zero}
   = & \rev(\rev(x)) \\
 &     \href{@rev@#thm-rev-involution}
   = & x
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \takeBut(\next(k))(\nil) \\
 &     \href{@takebut-dropbut@#def-takebut}
   = & \rev(\drop(\next(k))(\rev(\nil))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\drop(\next(k))(\nil)) \\
 & = & \rev(\nil) \\
 &     \href{@rev@#cor-rev-nil}
   = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \takeBut(\next(k))(\snoc(a,x)) \\
 &     \href{@takebut-dropbut@#def-takebut}
   = & \rev(\drop(\next(k))(\rev(\snoc(a,x)))) \\
 &     \href{@rev@#thm-rev-snoc}
   = & \rev(\drop(\next(k))(\cons(a,\rev(x)))) \\
 & = & \rev(\drop(k)(\rev(x))) \\
 &     \href{@takebut-dropbut@#def-takebut}
   = & \takeBut(k,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\takeBut$ is a prefix.

:::::: theorem :::::
[]{#thm-takebut-prefix}
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\prefix(\takeBut(k,x),x) = \btrue.$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \prefix(\takeBut(k,x),x) \\
 &     \href{@takebut-dropbut@#def-takebut}
   = & \prefix(\rev(\drop(k,\rev(x))),x) \\
 &     \href{@rev@#thm-rev-involution}
   = & \prefix(\rev(\drop(k,\rev(x))),\rev(\rev(x))) \\
 & = & \suffix(\drop(k,\rev(x)),\rev(x)) \\
 &     \href{@take-drop@#thm-drop-suffix}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeBut_prefix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_prefix _ _ =
>   testName "prefix(takeBut(k,x),x) == true" $
>   \k x -> eq (prefix (takeBut k x) x) true

::::::::::::::::::::
::::::::::::::::::::

So $\takeBut$ is a sublist:

:::::: theorem :::::
[]{#thm-takebut-sublist}
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\sublist(\takeBut(k,x),x) = \btrue.$$

::: proof ::::::::::
We have $$\prefix(\takeBut(k,x),x) = \btrue,$$ so $$\infix(\takeBut(k,x),x) = \btrue,$$ so $$\sublist(\takeBut(k,x),x) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeBut_sublist :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_sublist _ _ =
>   testName "sublist(takeBut(k,x),x) == true" $
>   \k x -> eq (sublist (takeBut k x) x) true

::::::::::::::::::::
::::::::::::::::::::

Now for $\dropBut$.

:::::: theorem :::::
[]{#thm-dropbut-zero}[]{#thm-dropbut-next-nil}[]{#thm-dropbut-next-snoc}
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have the following.

1. $\dropBut(\zero,x) = \nil$.
2. $\dropBut(\next(k),\nil) = \nil$.
3. $\dropBut(\next(k),\snoc(a,x)) = \snoc(a,\dropBut(k,x))$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \dropBut(\zero,x) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \rev(\take(\zero,\rev(x))) \\
 &     \href{@take-drop@#cor-take-zero}
   = & \rev(\nil) \\
 &     \href{@rev@#cor-rev-nil}
   = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \dropBut(k,\nil) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \rev(\take(k,\rev(\nil))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\take(k,\nil)) \\
 & = & \rev(\nil) \\
 &     \href{@rev@#cor-rev-nil}
   = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \dropBut(\next(k),\snoc(a,x)) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \rev(\take(\next(k),\rev(\snoc(a,x)))) \\
 &     \href{@rev@#thm-rev-snoc}
   = & \rev(\take(\next(k),\cons(a,\rev(x)))) \\
 & = & \rev(\cons(a,\take(k,\rev(x)))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \snoc(a,\rev(\take(k,\rev(x)))) \\
 & = & \snoc(a,\dropBut(k,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\dropBut$ is a $\suffix$.

:::::: theorem :::::
[]{#thm-dropbut-suffix}
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\suffix(\dropBut(k,x),x) = \btrue.$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \suffix(\dropBut(k,x),x) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \suffix(\rev(\take(k,\rev(x))),x) \\
 &     \href{@rev@#thm-rev-involution}
   = & \suffix(\rev(\take(k,\rev(x))),\rev(\rev(x))) \\
 & = & \prefix(\take(k,\rev(x)),\rev(x)) \\
 &     \href{@take-drop@#thm-take-prefix}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_dropBut_suffix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_dropBut_suffix _ _ =
>   testName "suffix(dropBut(k,x),x) == true" $
>   \k x -> eq (suffix (dropBut k x) x) true

::::::::::::::::::::
::::::::::::::::::::

$\dropBut$ is idempotent.

:::::: theorem :::::
[]{#thm-dropbut-idempotent}
Let $A$ be a set. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\dropBut(k,\dropBut(k,x)) = \dropBut(k,x).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \dropBut(k,\dropBut(k,x)) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \dropBut(k,\rev(\take(k,\rev(x)))) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \rev(\take(k,\rev(\rev(\take(k,\rev(x)))))) \\
 &     \href{@rev@#thm-rev-involution}
   = & \rev(\take(k,\take(k,\rev(x)))) \\
 & = & \rev(\take(k,\rev(x))) \\
 &     \href{@takebut-dropbut@#def-dropbut}
   = & \dropBut(k,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_dropBut_idempotent :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_dropBut_idempotent _ _ =
>   testName "dropBut(k,dropBut(k,x)) == dropBut(k,x)" $
>   \k x -> eq (dropBut k (dropBut k x)) (dropBut k x)

::::::::::::::::::::
::::::::::::::::::::

Like $\take$ and $\drop$, $\takeBut$ and $\dropBut$ give a kind of $\cat$-factorization.

:::::: theorem :::::
[]{#thm-takebut-dropbut-cat}
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$x = \cat(\takeBut(k,x),\dropBut(k,x)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \cat(\takeBut(k,x),\dropBut(k,x)) \\
 & = & \cat(\rev(\drop(k,\rev(x))),\rev(\take(k,\rev(x)))) \\
 &     \href{@cat@#thm-rev-cat-antidistribute}
   = & \rev(\cat(\take(k,\rev(x)),\drop(k,\rev(x)))) \\
 & = & \rev(\rev(x)) \\
 &     \href{@rev@#thm-rev-involution}
   = & x
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeBut_dropBut_cat :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_takeBut_dropBut_cat _ _ =
>   testName "cat(takeBut(k,x),dropBut(k,x)) == x" $
>   \k x -> eq (cat (takeBut k x) (dropBut k x)) x

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_takebut_dropbut ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   ) => Int -> Int -> t a -> n -> IO ()
> _test_takebut_dropbut size cases t k = do
>   testLabel1 "takeBut & dropBut" t
> 
>   let args = testArgs size cases
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
>   _test_takebut_dropbut 20 100 (nil :: ConsList Bool)  (zero :: Unary)
>   _test_takebut_dropbut 20 100 (nil :: ConsList Unary) (zero :: Unary)
