---
title: Unzip
author: nbloomf
date: 2017-05-07
tags: arithmetic-made-difficult, literate-haskell
slug: unzip
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Unzip
>   ( unzip, _test_unzip, main_unzip
>   ) where
> 
> import Testing
> import Booleans
> import Tuples
> import NaturalNumbers
> import Lists
> import Map
> import Zip

Today we will define a kind of one-sided inverse of $\zip$, called $\unzip$. Recall that $\zip$ has signature $$\lists{A} \times \lists{B} \rightarrow \lists{A \times B}.$$ An inverse will then have signature $$\lists{A \times B} \rightarrow \lists{A} \times \lists{B},$$ and should "undo" the zipping. As usual we'd like to define this as a fold if possible; to that end we need $\varepsilon : \lists{A} \times \lists{B}$ and $$\varphi : (A \times B) \times (\lists{A} \times \lists{B}) \rightarrow \lists{A} \times \lists{B}$$ such that
$$\begin{eqnarray*}
 &   & (\nil,\nil) \\
 & = & \unzip(\nil) \\
 & = & \foldr(\varepsilon)(\varphi)(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & \varepsilon
\end{eqnarray*}$$
and if $\unzip(x) = (u,v)$, then
$$\begin{eqnarray*}
 &   & (\cons(a,u),\cons(b,v)) \\
 & = & \unzip(\cons((a,b),x)) \\
 & = & \foldr(\varepsilon)(\varphi)(\cons((a,b),x)) \\
 & = & \varphi((a,b),\foldr(\varepsilon)(\varphi)(x)) \\
 & = & \varphi((a,b),\unzip(x)) \\
 & = & \varphi((a,b),(u,v)).
\end{eqnarray*}$$
With this in mind, we define $\unzip$ like so.

:::::: definition ::
Let $A$ and $B$ be sets. Define $\varphi : (A \times B) \times (\lists{A} \times \lists{B}) \rightarrow \lists{A} \times \lists{B}$ by $$\varphi(u,z) = \tup(\cons(\fst(u),\fst(z)),\cons(\snd(u),\snd(z))).$$ We then define $\unzip : \lists{A \times B} \rightarrow \lists{A} \times \lists{B}$ by $$\unzip = \foldr(\tup(\nil)(\nil))(\varphi).$$

In Haskell:

> unzip :: (List t) => t (Pair a b) -> Pair (t a) (t b)
> unzip = foldr (tup nil nil) phi
>   where
>     phi u z = tup (cons (fst u) (fst z)) (cons (snd u) (snd z))

::::::::::::::::::::

Because $\unzip$ is defined as a $\foldr(\ast)(\ast)$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-unzip-nil}[]{#cor-unzip-cons}
Let $A$ and $B$ be sets. Then $\unzip$ is the unique map $f : \lists{A \times B} \rightarrow \lists{A} \times \lists{B}$ such that the following hold for all $a \in A$, $b \in B$, $x \in \lists{A}$, and $y \in \lists{B}$.
$$\left\{\begin{array}{l}
 f(\nil) = \tup(\nil)(\nil) \\
 f(\cons(u,z)) = \tup(\cons(\fst(u),\fst(z)))(\cons(\snd(u),\snd(z))).
\end{array}\right.$$

::: test :::::::::::

> _test_unzip_nil :: (List t, Equal (t a), Equal (t b))
>   => t a -> t b -> Test Bool
> _test_unzip_nil ta tb =
>   testName "unzip(nil) == (nil,nil)" $
>   eq (unzip nil) (tup (nil `withTypeOf` ta) (nil `withTypeOf` tb))
> 
> 
> _test_unzip_cons :: (List t, Equal (t a), Equal (t b))
>   => t a -> t b -> Test (a -> b -> t (Pair a b) -> Bool)
> _test_unzip_cons ta tb =
>   testName "unzip(cons((a,b),z)) == (cons(a,fst(unzip(z))),cons(b,snd(unzip(z))))" $
>   \a b z -> eq
>     (unzip (cons (tup a b) z))
>     (tup (cons a (fst (unzip z))) (cons b (snd (unzip z))))

::::::::::::::::::::
::::::::::::::::::::

Now $\zip$ undoes $\unzip$ as expected.

:::::: theorem :::::
[]{#thm-zip-unzip}
Let $A$ and $B$ be sets. For all $x \in \lists{A \times B}$, we have $$\uncurry(\zip)(\unzip(x)) = x.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \uncurry(\zip)(\unzip(x)) \\
 &     \hyp{x = \nil}
   = & \uncurry(\zip)(\unzip(\nil)) \\
 & = & \uncurry(\zip)(\tup(\nil)(\nil)) \\
 &     \href{@tuples@#def-uncurry}
   = & \zip(\nil)(\nil) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil \\
 &     \hyp{x = \nil}
   = & x
\end{eqnarray*}$$
as needed. Suppose now that the result holds for some $x$ and let $a \in A$ and $b \in B$. Let $(u,v) = \unzip(x)$. Now
$$\begin{eqnarray*}
 &   & \uncurry(\zip)(\unzip(\cons(\tup(a)(b),x))) \\
 & = & \uncurry(\zip)\tup(\cons(a,\fst(\unzip(x))))(\cons(b,\snd(\unzip(x)))) \\
 & = & \zip(\cons(a,\fst(\unzip(x))))(\cons(b,\snd(\unzip(x)))) \\
 &     \href{@zip@#cor-zip-cons-cons}
   = & \cons(\tup(a)(b),\zip(\fst(\unzip(x)),\snd(\unzip(x)))) \\
 & = & \cons(\tup(a)(b),\uncurry(\zip)(\unzip(x))) \\
 &     \hyp{\uncurry(\zip)(\unzip(x)) = x}
   = & \cons(\tup(a)(b),x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unzip_zip :: (List t, Equal a, Equal b, Equal (t (Pair a b)))
>   => t a -> t b -> Test (t (Pair a b) -> Bool)
> _test_unzip_zip _ _ =
>   testName "zip(unzip(x)) == x" $
>   \x -> eq ((uncurry zip) (unzip x)) x

::::::::::::::::::::
::::::::::::::::::::

(Note that the reverse composition $\unzip(\zip(x,y)) = (x,y),$ although it makes sense type-wise, does not hold for all $x$ and $y$ since $\zip$ truncates its longer argument.)

$\unzip$ interacts with $\tSwap$:

:::::: theorem :::::
[]{#thm-unzip-tSwap}
Let $A$ and $B$ be sets and $x \in \lists{A \times B}$. Then we have $$\tSwap(\unzip(x)) = \unzip(\map(\tSwap)(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \tSwap(\unzip(x)) \\
 &     \hyp{x = \nil}
   = & \tSwap(\unzip(\nil)) \\
 & = & \tSwap(\nil,\nil) \\
 & = & (\nil,\nil) \\
 & = & \unzip(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \unzip(\map(\tSwap)(\nil)) \\
 &     \hyp{x = \nil}
   = & \unzip(\map(\tSwap)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $(a,b) \in A \times B$. Suppose $(u,v) = \unzip(x)$; by the inductive hypothesis we have $(v,u) = \unzip(\map(\tSwap)(x))$. Now
$$\begin{eqnarray*}
 &   & \unzip(\map(\tSwap)(\cons((a,b),x))) \\
 & = & \unzip(\cons(\tSwap(a,b),\map(\tSwap)(x))) \\
 & = & \unzip(\cons((b,a),\map(\tSwap)(x))) \\
 & = & (\cons(b,v),\cons(a,u)) \\
 & = & \tSwap(\cons(a,u),\cons(b,v)) \\
 & = & \tSwap(\unzip(\cons((a,b),x)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_unzip_tswap :: (List t, Equal (t b), Equal (t a))
>   => t a -> t b -> Test (t (Pair a b) -> Bool)
> _test_unzip_tswap _ _ =
>   testName "tswap(unzip(x)) == unzip(map(tswap)(x))" $
>   \x -> eq (unzip (map tswap x)) (tswap (unzip x))

::::::::::::::::::::
::::::::::::::::::::

$\unzip$ interacts with $\tPair$.

:::::: theorem :::::
[]{#thm-unzip-tPair}
Let $A$, $B$, $U$, and $V$ be sets, with $f : A \rightarrow U$ and $g : B \rightarrow V$. For all $x \in \lists{A \times B}$ we have $$\unzip(\map(\tPair(f,g))(x)) = \tPair(\map(f),\map(g))(\unzip(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \unzip(\map(\tPair(f,g))(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \unzip(\nil) \\
 & = & \tup(\nil)(\nil) \\
 & = & \tup(\map(f)(\nil))(\map(g)(\nil)) \\
 & = & \tPair(\map(f),\map(g))(\nil,\nil) \\
 & = & \tPair(\map(f),\map(g))(\unzip(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $(a,b) \in A \times B$. Say $(u,v) = \unzip(x)$. Letting $\varphi$ be as in the definition of $\unzip$ and using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \tPair(\map(f),\map(g))(\unzip(\cons((a,b),x))) \\
 & = & \tPair(\map(f),\map(g))(\cons(a,u),\cons(b,v)) \\
 & = & (\map(f)(\cons(a,u)),\map(g)(\cons(b,v))) \\
 & = & (\cons(f(a),\map(f)(u)),\cons(g(b),\map(g)(v))) \\
 & = & \varphi((f(a),g(b)),(\map(f)(u),\map(g)(v))) \\
 & = & \varphi((f(a),g(b)),\tPair(\map(f),\map(g))(u,v)) \\
 & = & \varphi((f(a),g(b)),\tPair(\map(f),\map(g))(\unzip(x))) \\
 & = & \varphi((f(a),g(b)),\unzip(\map(\tPair(f,g))(x))) \\
 & = & \varphi(\tPair(f,g)(a,b),\unzip(\map(\tPair(f,g))(x))) \\
 & = & \varphi(\tPair(f,g)(a,b),\foldr((\nil,\nil))(\varphi)(\map(\tPair(f,g))(x))) \\
 & = & \foldr((\nil,\nil))(\varphi)(\cons(\tPair(f,g)(a,b),\map(\tPair(f,g))(x))) \\
 & = & \foldr((\nil,\nil))(\varphi)(\map(\tPair(f,g))(\cons((a,b),x))) \\
 & = & \unzip(\map(\tPair(f,g))(\cons((a,b),x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_unzip_tpair :: (List t, Equal (t b), Equal (t a))
>   => t a -> t b -> Test ((a -> a) -> (b -> b) -> t (Pair a b) -> Bool)
> _test_unzip_tpair _ _ =
>   testName "unzip(map(tpair(f,g))(x)) == tpair(map(f),map(g))(unzip(x))" $
>   \f g x -> eq (unzip (map (tpair f g) x)) (tpair (map f) (map g) (unzip x))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_unzip ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName b, Show b, Equal b, Arbitrary b, CoArbitrary b
>   , TypeName (t a), TypeName (t b), List t
>   , Equal (t (Pair a b)), Arbitrary (t a), Show (t a), Arbitrary (t b), Show (t b)
>   , Show (t (Pair a b)), Arbitrary (t (Pair a b)), Equal (t b), Equal (t a)
>   ) => Int -> Int -> t a -> t b -> IO ()
> _test_unzip size cases t u = do
>   testLabel2 "unzip" t u
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_unzip_nil t u)
>   runTest args (_test_unzip_cons t u)
>   runTest args (_test_unzip_zip t u)
>   runTest args (_test_unzip_tswap t u)
>   runTest args (_test_unzip_tpair t u)

Main:

> main_unzip :: IO ()
> main_unzip = do
>   _test_unzip 20 100 (nil :: ConsList Bool)  (nil :: ConsList Bool)
>   _test_unzip 20 100 (nil :: ConsList Unary) (nil :: ConsList Unary)
