---
title: TakeWhile and DropWhile
author: nbloomf
date: 2017-12-16
tags: arithmetic-made-difficult, literate-haskell
slug: takewhile-dropwhile
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module TakeWhileAndDropWhile
>   ( takeWhile, dropWhile
>   , _test_takewhile_dropwhile, main_takewhile_dropwhile
>   ) where
> 
> import Testing
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers
> import Plus
> import MaxAndMin
> import Lists
> import HeadAndTail
> import ConsumingFold
> import Snoc
> import Reverse
> import Cat
> import Length
> import Map
> import UnfoldN
> import Zip
> import PrefixAndSuffix
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

Today we'll define two functions, $\takeWhile$ and $\dropWhile$, similar to $\take$ and $\drop$, but instead of taking or dropping a prefix of some length, we will take or drop the longest prefix satisfying some predicate. We'd like $\takeBut$ to have a signature like $$\takeWhile : \bool^A \rightarrow {\lists{A}}^{\lists{A}}.$$

As usual, suppose $\takeWhile$ can be defined in terms of fold; say $$\takeWhile(p)(x) = \foldr{e}{\varphi}(x)$$ for some $e$ and $\varphi$. To make the types work out we need $e \in \lists{A}$ and $\varphi : A \times \lists{A} \rightarrow \lists{A}$. Thinking about the desired behavior for $\takeWhile$, we need

$$\begin{eqnarray*}
 &   & \nil \\
 & = & \takeWhile(p)(\nil) \\
 & = & \foldr{e}{\varphi}(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & e
\end{eqnarray*}$$

and

$$\begin{eqnarray*}
 &   & \bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil} \\
 & = & \takeWhile(p)(\cons(a,x)) \\
 & = & \foldr{e}{\varphi}(\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \varphi(a,\foldr{e}{\varphi}(x)) \\
 & = & \varphi(a,\takeWhile(p,x))
\end{eqnarray*}$$

With this in mind, we define $\takeWhile$ like so.

:::::: definition ::
Let $A$ be a set, with $p : A \rightarrow \bool$. Define $\varphi(p) : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(p)(a,x) = \left\{ \begin{array}{ll} \cons(a,x) & \mathrm{if}\ p(a) = \btrue \\ \nil & \mathrm{otherwise}. \end{array} \right.$$

We define $\takeWhile : \bool^A \times \lists{A} \rightarrow \lists{A}$ by $$\takeWhile(p,x) = \foldr{\nil}{\varphi(p)}(x).$$

In Haskell:

> takeWhile :: (List t) => (a -> Bool) -> t a -> t a
> takeWhile p = foldr nil phi
>   where
>     phi a x = if eq (p a) true
>       then cons a x
>       else nil

::::::::::::::::::::

As usual, since $\takeWhile$ is defined directly in terms of foldr it is the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\takeWhile$ is the unique function $$f : \bool^A \times \lists{A} \rightarrow \lists{A}$$ satisfying the following system of equations for all $p : A \rightarrow \bool$, $a \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(p,\nil) = \nil \\
 f(p,\cons(a,x)) = \bif{p(a)}{\cons(a,f(p,x))}{\nil}.
\end{array}\right.$$

::: test :::::::::::

> _test_takeWhile_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> Bool)
> _test_takeWhile_nil t =
>   testName "takeWhile(p)(nil) == nil" $
>   \p -> eq (takeWhile p nil) (nil `withTypeOf` t)
> 
> 
> _test_takeWhile_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_takeWhile_cons t =
>   testName "takeWhile(p)(cons(a,x)) == if(p(a),cons(a,takeWhile(p)(x),nil))" $
>   \p a x -> eq
>     (takeWhile p (cons a x))
>     (if p a then cons a (takeWhile p x) else nil)

::::::::::::::::::::
::::::::::::::::::::

$\takeWhile$ gives prefixes.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x \in \lists{A}$, we have $$\prefix(\takeWhile(p,x),x) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\takeWhile(p,\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. We have
$$\begin{eqnarray*}
 &   & \prefix(\takeWhile(p,\cons(a,x),\cons(a,x))) \\
 & = & \prefix(\bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil},\cons(a,x)) \\
 & = & \bif{p(a)}{\prefix(\cons(a,\takeWhile(p,x)),\cons(a,x))}{\prefix(\nil,\cons(a,x))} \\
 & = & \bif{p(a)}{\prefix(\takeWhile(p,x),x)}{\btrue} \\
 & = & \bif{p(a)}{\btrue}{\btrue} \\
 &     \href{@booleans@#thm-if-same}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeWhile_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_prefix _ =
>   testName "prefix(takeWhile(p,x),x) == true" $
>   \p x -> eq (prefix (takeWhile p x) x) true

::::::::::::::::::::
::::::::::::::::::::

So $\takeWhile$ also gives a sublists.

:::::: theorem :::::
Let $A$ be a set, with $p : A \rightarrow \bool$ and $x \in \lists{A}$. Then we have $$\sublist(\takeWhile(k,x),x) = \btrue.$$

::: proof ::::::::::
We have $$\prefix(\takeWhile(k,x),x) = \btrue,$$ so $$\infix(\takeWhile(k,x),x) = \btrue,$$ so $$\sublist(\takeWhile(k,x),x) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeWhile_sublist :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_sublist _ =
>   testName "sublist(takeWhile(p,x),x) == true" $
>   \p x -> eq (sublist (takeWhile p x) x) true

::::::::::::::::::::
::::::::::::::::::::

$\takeWhile$ is idempotent.

:::::: theorem :::::
Let $A$ be a set with $p : A \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\takeWhile(p,\takeWhile(p,x)) = \takeWhile(p,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,x)) \\
 & = & \takeWhile(p,\takeWhile(p,\nil)) \\
 & = & \takeWhile(p,\nil) \\
 & = & \takeWhile(p,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,\cons(a,x))) \\
 & = & \takeWhile(p,\cons(a,\takeWhile(p,x))) \\
 & = & \cons(a,\takeWhile(p,\takeWhile(p,x))) \\
 & = & \cons(a,\takeWhile(p,x)) \\
 & = & \takeWhile(p,\cons(a,x))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,\cons(a,x))) \\
 & = & \takeWhile(p,\nil) \\
 & = & \nil \\
 & = & \takeWhile(p,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeWhile_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_idempotent _ =
>   testName "takeWhile(p,takeWhile(p,x)) == takeWhile(p,x)" $
>   \p x -> eq (takeWhile p (takeWhile p x)) (takeWhile p x)

::::::::::::::::::::
::::::::::::::::::::

$\takeWhile$ commutes with itself (kind of).

:::::: theorem :::::
Let $A$ be a set with $p$ and $q$ mappings $A \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\takeWhile(p,\takeWhile(q,x)) = \takeWhile(q,\takeWhile(p,x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(q,x)) \\
 & = & \takeWhile(p,\takeWhile(q,\nil)) \\
 & = & \takeWhile(p,\nil) \\
 & = & \nil \\
 & = & \takeWhile(q,\nil) \\
 & = & \takeWhile(q,\takeWhile(p,\nil)) \\
 & = & \takeWhile(q,\takeWhile(p,x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(q,\cons(a,x))) \\
 & = & \takeWhile(p,\bif{q(a)}{\cons(a,\takeWhile(q,x))}{\nil}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{q(a)}{\takeWhile(p,\cons(a,\takeWhile(q,x)))}{\takeWhile(p,\nil)} \\
 & = & \bif{q(a)}{\bif{p(a)}{\cons(a,\takeWhile(p,\takeWhile(q,x)))}{\nil}}{\nil} \\
 & = & \bif{q(a)}{\bif{p(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\bif{p(a)}{\nil}{\nil}} \\
 &     \href{@booleans@#thm-ifnest}
   = & \bif{p(a)}{\bif{q(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\bif{q(a)}{\nil}{\nil}} \\
 & = & \bif{p(a)}{\bif{q(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\nil} \\
 & = & \bif{p(a)}{\takeWhile(q,\cons(a,\takeWhile(p,x)))}{\takeWhile(q,\nil)} \\
 &     \href{@booleans@#thm-iffunc}
   = & \takeWhile(q,\bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil}) \\
 & = & \takeWhile(q,\takeWhile(p,\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeWhile_commutes :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> (a -> Bool) -> t a -> Bool)
> _test_takeWhile_commutes _ =
>   testName "takeWhile(p,takeWhile(q,x)) == takeWhile(q,takeWhile(p,x))" $
>   \p q x ->
>     eq (takeWhile p (takeWhile q x)) (takeWhile q (takeWhile p x))

::::::::::::::::::::
::::::::::::::::::::

Now for $\dropWhile$. This function should drop the longest prefix satisfying some predicate, again with signature $\bool^A \times \lists{A} \rightarrow \lists{A}$. If we try defining this using foldr in the "obvious" way, we run into trouble, where the $\varphi$ parameter needs to have its argument and eat it too. (try it!) One way around this is the trick we used to define $\zip$.

Suppose $$\dropWhile(p,x) = \foldr{e}{\varphi}(x)(x)$$ for some $e$ and $\varphi$. To make the types work out, we need $$e \in \lists{A}^{\lists{A}}$$ and $$\varphi : A \times \lists{A}^{\lists{A}} \rightarrow \lists{A}^{\lists{A}};$$ now
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \dropWhile(p,\nil) \\
 & = & \foldr{e}{\varphi}(\nil)(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & e(\nil)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \varphi(a,\foldr{e}{\varphi}(x))(\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \foldr{e}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \dropWhile(p,\cons(a,x)) \\
 & = & \bif{p(a)}{\dropWhile(p,x)}{\cons(a,x)}
\end{eqnarray*}$$

(that last line is why using a plain fold doesn't work.) In cases like this, the consuming fold is handy.

:::::: definition ::
Let $A$ be a set with $p : A \rightarrow \bool$. Define $\sigma : A \times \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\sigma(a,x,y) = \bif{p(a)}{y}{\cons(a,x)}.$$ Now define $\dropWhile : \bool^A \rightarrow {\lists{A}}^{\lists{A}}$ by $$\dropWhile(p) = \cfoldr(\nil)(\sigma).$$

In Haskell:

> dropWhile :: (List t) => (a -> Bool) -> t a -> t a
> dropWhile p = cfoldr nil sigma
>   where
>     sigma a x y = if p a then y else cons a x

::::::::::::::::::::

Because $\dropWhile$ is defined as a consuming fold, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set, with $p$ a predicate on $A$. Then $\dropWhile(p)$ is the unique map $f : \lists{A} \rightarrow \lists{A}$ satisfying the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \bif{p(a)}{f(x)}{\cons(a,x)}
\end{array}\right.$$

::: test :::::::::::

> _test_dropWhile_nil :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> Bool)
> _test_dropWhile_nil t =
>   testName "dropWhile(p)(nil) == nil" $
>   \p -> eq (dropWhile p nil) (nil `withTypeOf` t)
> 
> 
> _test_dropWhile_cons :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> a -> t a -> Bool)
> _test_dropWhile_cons t =
>   testName "dropWhile(p)(cons(a,x)) == if(p(a),dropWhile(p)(x),cons(a,x))" $
>   \p a x -> eq
>     (dropWhile p (cons a x))
>     (if p a then dropWhile p x else cons a x)

::::::::::::::::::::
::::::::::::::::::::

Now $\dropBut$ is a $\suffix$:

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $p : A \rightarrow \bool$, we have $$\suffix(\dropWhile(p)(x),x) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \suffix(\dropWhile(p)(\nil),\nil) \\
 & = & \suffix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. By the inductive hypothesis we have $\suffix(\dropWhile(p)(x),x)$, so that $\suffix(\dropWhile(p)(x),\cons(a,x))$. Now
$$\begin{eqnarray*}
 &   & \suffix(\dropWhile(p)(\cons(a,x)),\cons(a,x)) \\
 & = & \suffix(\bif{p(a)}{\dropWhile(p)(x)}{\cons(a,x)},\cons(a,x)) \\
 & = & \bif{p(a)}{\suffix(\dropWhile(p)(x),\cons(a,x))}{\suffix(\cons(a,x),\cons(a,x))} \\
 & = & \bif{p(a)}{\btrue}{\btrue} \\
 &     \href{@booleans@#thm-if-same}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_dropWhile_suffix :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_dropWhile_suffix _ =
>   testName "suffix(dropWhile(p)(x),x) == true" $
>   \p x -> eq (suffix (dropWhile p x) x) true

::::::::::::::::::::
::::::::::::::::::::

Like $\take$ and $\drop$, $\takeWhile$ and $\dropWhile$ give a kind of $\cat$-factorization.

:::::: theorem :::::
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x \in \lists{A}$ we have $$x = \cat(\takeWhile(p)(x),\dropWhile(p)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \cat(\takeWhile(p)(\nil),\dropWhile(p)(\nil)) \\
 & = & \cat(\nil,\nil) \\
 &     \href{@cat@#cor-cat-nil}
   = & \nil
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \cat(\takeWhile(p)(\cons(a,x)),\dropWhile(p)(\cons(a,x))) \\
 & = & \cat(\bif{p(a)}{\cons(a,\takeWhile(p)(x))}{\nil},\bif{p(a)}{\dropWhile(x)}{\cons(a,x)}) \\
 & = & \bif{p(a)}{\cat(\cons(a,\takeWhile(p)(x)),\dropWhile(p)(x))}{\cat(\nil,\cons(a,x))} \\
 & = & \bif{p(a)}{\cons(a,\cat(\takeWhile(p)(x)),\dropWhile(p)(x))}{\cons(a,x)} \\
 & = & \bif{p(a)}{\cons(a,x)}{\cons(a,x)} \\
 &     \href{@booleans@#thm-if-same}
   = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_takeWhile_dropWhile_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_dropWhile_cat _ =
>   testName "cat(takeWhile(p)(x),dropWhile(p)(x)) == x" $
>   \p x -> eq (cat (takeWhile p x) (dropWhile p x)) x

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_takewhile_dropwhile ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_takewhile_dropwhile t k size cases = do
>   testLabel1 "takeWhile & dropWhile" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_takeWhile_nil t)
>   runTest args (_test_takeWhile_cons t)
>   runTest args (_test_takeWhile_prefix t)
>   runTest args (_test_takeWhile_sublist t)
>   runTest args (_test_takeWhile_idempotent t)
>   runTest args (_test_takeWhile_commutes t)
> 
>   runTest args (_test_dropWhile_nil t)
>   runTest args (_test_dropWhile_cons t)
>   runTest args (_test_dropWhile_suffix t)
> 
>   runTest args (_test_takeWhile_dropWhile_cat t)

Main:

> main_takewhile_dropwhile :: IO ()
> main_takewhile_dropwhile = do
>   _test_takewhile_dropwhile (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_takewhile_dropwhile (nil :: ConsList Unary) (zero :: Unary) 20 100
