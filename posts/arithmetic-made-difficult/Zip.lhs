---
title: Zip
author: nbloomf
date: 2017-05-06
tags: arithmetic-made-difficult, literate-haskell
slug: zip
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Zip
>   ( zip, _test_zip, main_zip
>   ) where
> 
> import Testing
> import Tuples
> import NaturalNumbers
> import MaxAndMin
> import Lists
> import DoubleFold
> import Length
> import Map

Today we'll define a really useful function on lists called $\zip$. This map will take two lists, one in $\lists{A}$ and one in $\lists{B}$, and return a list in $\lists{A \times B}$. In progress, $\zip$ping two lists looks something like this:
$$\begin{array}{ccccccccccc}
          &   &           &   &           &           & a_4 & - & a_5 &   &     \\
          &   &           &   &           & \diagup   &     &   &     &   &     \\
(a_1,b_1) & - & (a_2,b_2) & - & (a_3,b_3) &           &     &   &     &   &     \\
          &   &           &   &           & \diagdown &     &   &     &   &     \\
          &   &           &   &           &           & b_4 & - & b_5 & - & b_6
\end{array}$$
Hence the name $\zip$ -- it looks like a zipper in action. A big question has to be resolved. It seems clear what $\zip$ should do if we give it two lists with the same length. But what if we try to zip two lists of different lengths? I can see two basic strategies. On one hand we can just truncate to the length of the shortest list. Another idea is to *pad* the shorter list to the length of the longer. These are both useful but essentially different behaviors, so we will define two different functions to handle them. The truncation strategy will be called $\zip$ and the padding strategy will be called $\zipPad$.

:::::: definition ::
Let $A$ and $B$ be sets. Define $\delta : \lists{B} \rightarrow \lists{A \times B}$ by $$\delta(y) = \nil,$$ $\psi : A \times \lists{A \times B} \rightarrow \lists{A \times B}$ by $$\psi(a,z) = \nil,$$ and $\chi : A \times B \times \lists{B} \times \lists{A \times B} \times \lists{A \times B} \rightarrow \lists{A \times B}$ by $$\chi(a,b,y,z,w) = \cons((a,b),z).$$ Now define $$\zip : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$$ by $$\zip = \dfoldr(\delta)(\psi)(\chi).$$

In Haskell:

> zip :: (List t) => t a -> t b -> t (Pair a b)
> zip = dfoldr delta psi chi
>   where
>     delta _ = nil
>     psi _ _ = nil
>     chi a b _ z _ = cons (tup a b) z

::::::::::::::::::::

Since $\zip$ is defined in terms of $\dfoldr$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-zip-nil-left}[]{#cor-zip-cons-nil}[]{#cor-zip-cons-cons}
Let $A$ and $B$ be sets. Then $\zip$ is the unique solution $f : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$ to the following equations for all $a \in A$, $b \in B$, $x \in \lists{A}$, and $y \in \lists{B}$.
$$\left\{\begin{array}{l}
 f(\nil,y) = \nil \\
 f(\cons(a,x),\nil) = \nil \\
 f(\cons(a,x),\cons(b,y)) = \cons((a,b),f(x,y))
\end{array}\right.$$

::: test :::::::::::

> _test_zip_nil_list :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (t b -> Bool)
> _test_zip_nil_list ta _ =
>   testName "zip(nil,y) == nil" $
>   \y -> eq (zip (nil `withTypeOf` ta) y) nil
> 
> 
> _test_zip_cons_nil :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> t a -> Bool)
> _test_zip_cons_nil _ tb =
>   testName "zip(cons(a,x),nil) == nil" $
>   \a x -> eq (zip (cons a x) (nil `withTypeOf` tb)) nil
> 
> 
> _test_zip_cons_cons :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> t a -> b -> t b -> Bool)
> _test_zip_cons_cons _ _ =
>   testName "zip(cons(a,x),cons(b,y)) == cons((a,b),zip(x,y))" $
>   \a x b y -> eq (zip (cons a x) (cons b y)) (cons (tup a b) (zip x y))

::::::::::::::::::::
::::::::::::::::::::

Implicit in the universal property is that $\nil$ is a right zero for $\zip$.

:::::: theorem :::::
[]{#thm-zip-nil-right}
For all $x \in \lists{A}$ we have $\zip(x,\nil) = \nil$.

::: proof ::::::::::
We have two possibilities for $x$. If $x = \nil$, then
$$\begin{eqnarray*}
 &   & \zip(\nil,\nil) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil
\end{eqnarray*}$$
and if $x = \cons(a,y)$, we have
$$\begin{eqnarray*}
 &   & \zip(\cons(a,y),\nil) \\
 &     \href{@zip@#cor-zip-cons-nil}
   = & \nil
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_zip_nil_right :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (t a -> Bool)
> _test_zip_nil_right _ tb =
>   testName "zip(x,nil) == nil" $
>   \x -> eq (zip x (nil `withTypeOf` tb)) nil

::::::::::::::::::::
::::::::::::::::::::

Now $\compose(\map(\tSwap))(\zip) = \compose(\zip)(\tSwap)$.

:::::: theorem :::::
[]{#thm-zip-tSwap}
Let $A$ and $B$ be sets. Then for all $x \in \lists{A}$ and $y \in \lists{B}$ we have $$\map(\tSwap)(\zip(x,y)) = \zip(y,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zip(\nil,y)) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \map(\tSwap)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \zip(y,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y \in \lists{B}$ for some $x \in \lists{A}$, and let $a \in A$. Now we consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zip(\cons(a,x),y)) \\
 &     \let{y = \nil}
   = & \map(\tSwap)(\zip(\cons(a,x),\nil)) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \map(\tSwap)(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \zip(\nil,\cons(a,x)) \\
 &     \let{y = \nil}
   = & \zip(y,\cons(a,x))
\end{eqnarray*}$$
as needed. If $y = \cons(b,z)$, using the induction hypotheses, we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zip(\cons(a,x),y)) \\
 &     \let{y = \cons(b,z)}
   = & \map(\tSwap)(\zip(\cons(a,x),\cons(b,z))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \map(\tSwap)(\cons(\tup(a)(b),\zip(x,z))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(\tSwap(\tup(a)(b)),\map(\tSwap)(\zip(x,z))) \\
 &     \href{@tuples@#thm-tSwap-swap}
   = & \cons(\tup(b)(a),\map(\tSwap)(\zip(x,z))) \\
 &     \hyp{\map(\tSwap)(\zip(x,z)) = \zip(z,x)}
   = & \cons(\tup(b)(a),\zip(z,x)) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \zip(\cons(b,z),\cons(a,x)) \\
 &     \let{y = \cons(b,z)}
   = & \zip(y,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zip_tswap :: (List t, Equal (t (Pair b a)))
>   => t a -> t b -> Test (t a -> t b -> Bool)
> _test_zip_tswap _ _ =
>   testName "map(tswap)(zip(x,y)) == zip(y,x)" $
>   \x y -> eq (map tswap (zip x y)) (zip y x)

::::::::::::::::::::
::::::::::::::::::::

And $\map(\tPair(f,g)) \circ \zip = \zip \circ \tPair(\map(f),\map(g))$.

:::::: theorem :::::
[]{#thm-map-tPair}
Let $A$, $B$, $U$, and $V$ be sets, with functions $f : A \rightarrow U$ and $g : B \rightarrow V$. Then for all $x \in \lists{A}$ and $y \in \lists{B}$, we have $$\map(\tPair(f,g))(\zip(x,y)) = \zip(\map(f)(x),\map(g)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zip(\nil,y)) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \map(\tPair(f,g))(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \zip(\nil,\map(g)(y)) \\
 &     \href{@map@#cor-map-nil}
   = & \zip(\map(f)(\nil),\map(g)(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for all $y$ for some $x \in \lists{A}$, and let $a \in A$. We now consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zip(\cons(a,x),\nil)) \\
 &     \let{y = \nil}
   = & \map(\tPair(f,g))(\zip(\cons(a,x),\nil)) \\
 &     \href{@zip@#cor-zip-cons-nil}
   = & \map(\tPair(f,g))(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \zip(\map(f)(\cons(a,x)),\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \zip(\map(f)(\cons(a,x)),\map(g)(\nil)) \\
 &     \let{y = \nil}
   = & \zip(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed. If $y = \cons(b,z)$, using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zip(\cons(a,x),y)) \\
 &     \let{y = \cons(b,z)}
   = & \map(\tPair(f,g))(\zip(\cons(a,x),\cons(b,z))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \map(\tPair(f,g))(\cons(\tup(a)(b),\zip(x,z))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(\tPair(f,g)(\tup(a)(b)),\map(\tPair(f,g))(\zip(x,z))) \\
 &     \hyp{\map(\tPair(f,g))(\zip(x,y)) = \zip(\map(f)(x))(\map(g)(y))}
   = & \cons(\tPair(f,g)(\tup(a)(b)),\zip(\map(f)(x),\map(g)(z))) \\
 &     \href{@tuples@#thm-tPair-tup}
   = & \cons(\tup(f(a))(g(b)),\zip(\map(f)(x),\map(g)(z))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \zip(\cons(f(a),\map(f)(x)),\cons(g(b),\map(g)(z))) \\
 &     \href{@map@#cor-map-cons}
   = & \zip(\map(f)(\cons(a,x)),\cons(g(b),\map(g)(z))) \\
 &     \href{@map@#cor-map-cons}
   = & \zip(\map(f)(\cons(a,x)),\map(g)(\cons(b,z))) \\
 &     \let{y = \cons(b,z)}
   = & \zip(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zip_tpair :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test ((a -> a) -> (b -> b) -> t a -> t b -> Bool)
> _test_zip_tpair _ _ =
>   testName "map(tpair(f,g))(zip(x,y)) == zip(map(f)(x),map(g)(y))" $
>   \f g x y -> eq (map (tpair f g) (zip x y)) (zip (map f x) (map g y))

::::::::::::::::::::
::::::::::::::::::::

$\zip$ interacts with $\length$.

:::::: theorem :::::
[]{#thm-length-zip}
Let $A$ and $B$ be sets, with $x \in \lists{A}$ and $y \in \lists{B}$. Then $$\length(\zip(x,y)) = \nmin(\length(x),\length(y)).$$

::: proof ::::::::::
We proceed by list induction on $y$. For the base case $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,\nil)) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \length(\nil) \\
 &     \href{@length@#cor-length-nil}
   = & \zero \\
 & = & \nmin(\length(x),\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \nmin(\length(x),\length(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $y$ and let $b \in B$. We consider two cases: either $x = \nil$ or $x = \cons(a,z)$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,\cons(b,y))) \\
 & = & \length(\zip(\nil,\cons(b,y))) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \length(\nil) \\
 &     \href{@length@#cor-length-nil}
   = & \zero \\
 &     \href{@max-min@#thm-min-zero-left}
   = & \nmin(\zero,\length(\cons(b,y))) \\
 & = & \nmin(\length(\nil),\length(\cons(b,y))) \\
 & = & \nmin(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed. Suppose $x = \cons(a,z)$; now we have
$$\begin{eqnarray*}
 &   & \length(\zip(x,\cons(b,y))) \\
 &     \let{x = \cons(a,z)}
   = & \length(\zip(\cons(a,z),\cons(b,y))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \length(\cons(\tup(a)(b),\zip(z,y))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\zip(z)(y))) \\
 &     \href{@zip@#thm-length-zip}
   = & \next(\nmin(\length(z),\length(y))) \\
 &     \href{@max-min@#thm-next-min-distribute}
   = & \nmin(\next(\length(z)),\next(\length(y))) \\
 &     \href{@length@#cor-length-cons}
   = & \nmin(\length(\cons(a,z)),\next(\length(y))) \\
 &     \href{@length@#cor-length-cons}
   = & \nmin(\length(\cons(a,z)),\length(\cons(b,y))) \\
 &     \let{x = \cons(a,z)}
   = & \nmin(\length(x),\length(\cons(b,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zip_length :: (List t, Natural n, Equal n)
>   => t a -> t b -> n -> Test (t a -> t b -> Bool)
> _test_zip_length _ _ n =
>   testName "length(zip(x,y)) == min(length(x),length(y))" $
>   \x y -> eq
>     ((length (zip x y)) `withTypeOf` n)
>     (min (length x) (length y))

::::::::::::::::::::
::::::::::::::::::::

$\zip$ is kind of associative.

:::::: theorem :::::
[]{#thm-zip-assocL}[]{#thm-zip-assocR}
Let $A$, $B$, and $C$ be sets, with $x \in \lists{A}$, $y \in \lists{B}$, and $z \in \lists{C}$. Then the following hold.

1. $\zip(\zip(x,y),z) = \map(\tAssocL)(\zip(x,\zip(y,z)))$.
2. $\zip(x,\zip(y,z)) = \map(\tAssocR)(\zip(\zip(x,y),z))$.

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \zip(\zip(\nil,y),z) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \zip(\nil,z) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\tAssocL)(\nil) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \map(\tAssocL)(\zip(\nil,\zip(y,z)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 &     \let{y = \nil}
   = & \zip(\zip(\cons(a,x),\nil),z) \\
 &     \href{@zip@#cor-zip-cons-nil}
   = & \zip(\nil,z) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\tAssocL)(\nil) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \map(\tAssocL)(\zip(\cons(a,x),\nil)) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(\nil,z))) \\
 &     \let{y = \nil}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed. Similarly, if $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 &     \let{z = \nil}
   = & \zip(\zip(\cons(a,x),y),\nil) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\tAssocL)(\nil) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \map(\tAssocL)(\zip(\cons(a,x),\nil)) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(y,\nil))) \\
 &     \let{z = \nil}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,u)$ and $z = \cons(c,v)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \zip(\zip(\cons(a,x),y),z) \\
 &     \let{y = \cons(b,u)}
   = & \zip(\zip(\cons(a,x),\cons(b,u)),z) \\
 &     \let{z = \cons(c,v)}
   = & \zip(\zip(\cons(a,x),\cons(b,u)),\cons(c,v)) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \zip(\cons(\tup(a)(b),\zip(x,u)),\cons(c,v)) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \cons(\tup(\tup(a)(b))(c),\zip(\zip(x,u),v)) \\
 &     \href{@tuples@#thm-tAssocL-tup}
   = & \cons(\tAssocL(\tup(a)(\tup(b)(c))),\zip(\zip(x,u),v)) \\
 &     \hyp{\zip(\zip(x,u),v) = \map(\tAssocL)(\zip(x,\zip(u,v)))}
   = & \cons(\tAssocL(\tup(a)(\tup(b)(c))),\map(\tAssocL)(\zip(x,\zip(u,v)))) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\tAssocL)(\cons(\tup(a)(\tup(b)(c)),\zip(x,\zip(u,v)))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \map(\tAssocL)(\zip(\cons(a,x),\cons(\tup(b)(c),\zip(u,v)))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(\cons(b,u),\cons(c,v)))) \\
 &     \let{y = \cons(b,u)}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(y,\cons(c,v)))) \\
 &     \let{z = \cons(c,v)}
   = & \map(\tAssocL)(\zip(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \zip(x,\zip(y,z)) \\
 &     \href{@functions@#def-id}
   = & \id(\zip(x,\zip(y,z))) \\
 &     \href{@map@#thm-map-id}
   = & \map(\id)(\zip(x,\zip(y,z))) \\
 &     \href{@tuples@#thm-tAssocR-tAssocL}
   = & \map(\compose(\tAssocR)(\tAssocL))(\zip(x,\zip(y,z))) \\
 &     \href{@map@#thm-map-compose}
   = & \compose(\map(\tAssocR))(\map(\tAssocL))(\zip(x,\zip(y,z))) \\
 &     \href{@functions@#def-compose}
   = & \map(\tAssocR)(\map(\tAssocL)(\zip(x,\zip(y,z)))) \\
 &     \href{@zip@#thm-zip-assocL}
   = & \map(\tAssocR)(\zip(\zip(x,y),z)) 
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_zip_zip_left :: (List t, Equal (t (Pair (Pair a a) a)))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_zip_zip_left _ =
>   testName "zip(zip(x,y),z) == map(tassocL)(zip(x,zip(y,z)))" $
>   \x y z -> eq (zip (zip x y) z) (map tassocL (zip x (zip y z)))
> 
> 
> _test_zip_zip_right :: (List t, Equal (t (Pair a (Pair a a))))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_zip_zip_right _ =
>   testName "zip(zip(x,y),z) == map(tassocR)(zip(x,zip(y,z)))" $
>   \x y z -> eq (zip x (zip y z)) (map tassocR (zip (zip x y) z))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_zip ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName b, Equal b, Show b, Arbitrary b, CoArbitrary b
>   , TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t a), TypeName (t b), List t, Equal (t a), Show (t a), Arbitrary (t a)
>   , Equal (t b), Show (t b), Arbitrary (t b), Equal (t (Pair a b)), Equal (t (Pair b a))
>   , Equal (t (Pair a (Pair a a))), Equal (t (Pair (Pair a a) a))
>   ) => Int -> Int -> t a -> t b -> n -> IO ()
> _test_zip size cases t u n = do
>   testLabel3 "zip" t u n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_zip_nil_list t u)
>   runTest args (_test_zip_cons_nil t u)
>   runTest args (_test_zip_cons_cons t u)
>   runTest args (_test_zip_nil_right t u)
>   runTest args (_test_zip_tswap t u)
>   runTest args (_test_zip_tpair t u)
>   runTest args (_test_zip_length t u n)
>   runTest args (_test_zip_zip_left t)
>   runTest args (_test_zip_zip_right t)

Main:

> main_zip :: IO ()
> main_zip = do
>   _test_zip 20 100 (nil :: ConsList Bool)  (nil :: ConsList Bool)  (zero :: Unary)
>   _test_zip 20 100 (nil :: ConsList Unary) (nil :: ConsList Unary) (zero :: Unary)
