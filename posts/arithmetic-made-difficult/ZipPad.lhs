---
title: ZipPad
author: nbloomf
date: 2018-01-06
tags: arithmetic-made-difficult, literate-haskell
slug: zippad
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module ZipPad
>   ( zipPad, _test_zipPad, main_zipPad
>   ) where
> 
> import Testing
> import Flip
> import Tuples
> import NaturalNumbers
> import MaxAndMin
> import Lists
> import DoubleFold
> import Length
> import Map

Now to define $\zipPad$, an alternate interpretation of $\zip$.

:::::: definition ::
Let $A$ and $B$ be sets, with $u \in A$ and $v \in B$. Define $\delta : \lists{B} \rightarrow \lists{A \times B}$ by $$\delta(y) = \map(\tup(u))(y),$$ $\psi : A \times \lists{A \times B} \rightarrow \lists{A \times B}$ by $$\psi(a,z) = \cons((a,v),z),$$ and $\chi : A \times B \times \lists{B} \times \lists{A \times B} \times \lists{A \times B} \rightarrow \lists{A \times B}$ by $$\chi(a,b,y,z,w) = \cons((a,b),z).$$ We then define $\zipPad(u,v) : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$ by $$\zipPad(u,v) = \dfoldr(\delta)(\psi)(\chi).$$

In Haskell:

> zipPad :: (List t) => a -> b -> t a -> t b -> t (Pair a b)
> zipPad u v = dfoldr delta psi chi
>   where
>     delta y = map (tup u) y
>     psi a z = cons (tup a v) z
>     chi a b _ z _ = cons (tup a b) z

::::::::::::::::::::

Since $\zipPad(u,v)$ is defined as a $\dfoldr$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-zippad-nil-left}[]{#cor-zippad-cons-nil}[]{#cor-zippad-cons-cons}
Let $A$ and $B$ be sets. Then $\zip$ is the unique solution $f : \lists{A} \times \lists{B} \rightarrow \lists{A \times B}$ to the following equations for all $a \in A$, $b \in B$, $x \in \lists{A}$, and $y \in \lists{B}$.
$$\left\{\begin{array}{l}
 f(\nil,y) = \map(\tup(u))(y) \\
 f(\cons(a,x),\nil) = \cons(\tup(a)(v),f(x,nil)) \\
 f(\cons(a,x),\cons(b,y)) = \cons(\tup(a)(b),f(x,y))
\end{array}\right.$$

::: test :::::::::::

> _test_zipPad_nil_list :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> b -> t b -> Bool)
> _test_zipPad_nil_list ta _ =
>   testName "zipPad(u,v)(nil,y) == map(tupL(u))(y)" $
>   \u v y -> eq (zipPad u v (nil `withTypeOf` ta) y) (map (tup u) y)
> 
> 
> _test_zipPad_cons_nil :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> b -> a -> t a -> Bool)
> _test_zipPad_cons_nil _ tb =
>   testName "zipPad(u,v)(cons(a,x),nil) == nil" $
>   \u v a x -> eq
>     (zipPad u v (cons a x) (nil `withTypeOf` tb))
>     (cons (tup a v) (zipPad u v x nil))
> 
> 
> _test_zipPad_cons_cons :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> b -> a -> t a -> b -> t b -> Bool)
> _test_zipPad_cons_cons _ _ =
>   testName "zipPad(u,v)(cons(a,x),cons(b,y)) == cons((a,b),zipPad(u,v)(x,y))" $
>   \u v a x b y -> eq (zipPad u v (cons a x) (cons b y)) (cons (tup a b) (zipPad u v x y))

::::::::::::::::::::
::::::::::::::::::::

$\zipPad$ with a nil right argument is a $\map$.

:::::: theorem :::::
[]{#thm-zippad-nil-right}
Let $A$ and $B$ be sets, with $u \in A$ and $v \in B$. For all $x \in \lists{A}$, we have 
$$\zipPad(u,v)(x,\nil) = \map(\flip(\tup)(v))(x)$.

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad(u,v)(\nil,\nil) \\
 &     \href{@zippad@#cor-zippad-nil-left}
   = & \map(\tup(u))(\nil) \\
 &     \href{@map@#cor-map-nil}
   = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\flip(\tup)(v))(\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \zipPad(u,v)(\cons(a,x),\nil) \\
 &     \href{@zippad@#cor-zippad-cons-nil}
   = & \cons(\tup(a)(v),\zipPad(u,v)(x,\nil)) \\
 &     \href{@flip@#def-flip}
   = & \cons(\flip(\tup)(v)(a),\zipPad(u,v)(x,\nil)) \\
 &     \hyp{\zipPad(u,v)(x,\nil) = \map(\flip(\tup)(v))(x)}
   = & \cons(\flip(\tup)(v)(a),\map(\flip(\tup)(v))(x)) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\flip(\tup)(v))(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zipPad_nil_right :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test (a -> b -> t a -> Bool)
> _test_zipPad_nil_right _ _ =
>   testName "zipPad(u,v)(x,nil) == map(tupR(v))(x)" $
>   \u v x -> eq (zipPad u v x nil) (map ((flip tup) v) x)

::::::::::::::::::::
::::::::::::::::::::

$\zipPad$ interacts with $\tSwap$.

:::::: theorem :::::
[]{#thm-zippad-tSwap}
Let $A$ and $B$ be sets. Then for all $u \in A$, $v \in B$, $x \in \lists{A}$, and $y \in \lists{B}$ we have $$\map(\tSwap)(\zipPad(u,v)(x,y)) = \zipPad(v,u)(y,x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zipPad(u,v)(\nil,y)) \\
 &     \href{@zippad@#cor-zippad-nil-left}
   = & \map(\tSwap)(\map(\tup(u))(y)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\map(\tSwap))(\map(\tup(u)))(y) \\
 &     \href{@map@#thm-map-compose}
   = & \map(\compose(\tSwap)(\tup(u)))(y) \\
 & = & \map(\flip(\tup)(u))(y) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \zipPad(v,u)(y,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we consider two cases for $y$; either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zipPad(u,v)(\cons(a,x),y)) \\
 & = & \map(\tSwap)(\zipPad(u,v)(\cons(a,x),\nil)) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \map(\tSwap)(\map(\flip(\tup)(v))(\cons(a,x))) \\
 &     \href{@functions@#def-compose}
   = & \compose(\map(\tSwap))(\map(\flip(\tup)(v)))(\cons(a,x)) \\
 & = & \map(\compose(\tSwap)(\flip(\tup)(v)))(\cons(a,x)) \\
 & = & \map(\tup(v))(\cons(a,x)) \\
 & = & \zipPad(u,v)(\nil,\cons(a,x))
\end{eqnarray*}$$
as needed. Finally, suppose $y = \cons(b,w)$. Then we have
$$\begin{eqnarray*}
 &   & \map(\tSwap)(\zipPad(u,v)(\cons(a,x),y)) \\
 &     \let{y = \cons(b,w)}
   = & \map(\tSwap)(\zipPad(u,v)(\cons(a,x),\cons(b,w))) \\
 & = & \map(\tSwap)(\cons(\tup(a)(b),\zipPad(u,v)(x,w))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(\tSwap(\tup(a)(b)),\map(\tSwap)(\zipPad(u,v)(x,w))) \\
 &     \href{@tuples@#thm-tSwap-swap}
   = & \cons(\tup(b)(a),\map(\tSwap)(\zipPad(u,v)(x,w))) \\
 & = & \cons(\tup(b)(a),\zipPad(v,u)(w,x)) \\
 &     \href{@zippad@#cor-zippad-cons-cons}
   = & \zipPad(v,u)(\cons(b,w),\cons(a,x)) \\
 &     \let{y = \cons(b,w)}
   = & \zipPad(v,u)(y,\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zipPad_tswap :: (List t, Equal (t (Pair b a)))
>   => t a -> t b -> Test (a -> b -> t a -> t b -> Bool)
> _test_zipPad_tswap _ _ =
>   testName "map(tswap)(zipPad(u,v)(x,y)) == zipPad(v,u)(y,x)" $
>   \u v x y -> eq (map tswap (zipPad u v x y)) (zipPad v u y x)

::::::::::::::::::::
::::::::::::::::::::

$\zipPad$ interacts with $\tPair$.

:::::: theorem :::::
[]{#thm-zippad-map-tPair}
Let $A$, $B$, $U$, and $V$ be sets, with functions $f : A \rightarrow U$ and $g : B \rightarrow V$. Then for all $u \in A$, $v \in B$, $x \in \lists{A}$, and $y \in \lists{B}$, we have $$\map(\tPair(f,g))(\zipPad(u,v)(x,y)) = \zipPad(f(u),g(v))(\map(f)(x),\map(g)(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zipPad(u,v)(x,y)) \\
 &     \let{x = \nil}
   = & \map(\tPair(f,g))(\zipPad(u,v)(\nil,y)) \\
 & = & \map(\tPair(f,g))(\map(\tup(u))(y)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\map(\tPair(f,g)))(\map(\tup(u)))(y) \\
 & = & \map(\compose(\tPair(f,g))(\tup(u)))(y) \\
 & = & \map(\compose(\tup(f(u)))(g))(y) \\
 & = & \map(\tup(f(u)))(\map(g)(y)) \\
 &     \href{@zippad@#cor-zippad-nil-left}
   = & \zipPad(f(u),g(v))(\nil,\map(g)(y)) \\
 & = & \zipPad(f(u),g(v))(x,\map(g)(y))
\end{eqnarray*}$$
as needed. Now suppose the equality holds for some $x$ and let $a \in A$. We consider two cases for $y$; either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zipPad(u,v)(\cons(a,x),y)) \\
 & = & \map(\tPair(f,g))(\zipPad(u,v)(\cons(a,x),\nil)) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \map(\tPair(f,g))(\map(\flip(\tup)(v))(\cons(a,x))) \\
 &     \href{@functions@#def-compose}
   = & \compose(\map(\tPair(f,g)))(\map(\flip(\tup)(v)))(\cons(a,x)) \\
 & = & \map(\compose(\tPair(f,g))(\flip(\tup)(v)))(\cons(a,x)) \\
 & = & \map(\compose(\flip(\tup)(g(v)))(f))(\cons(a,x)) \\
 & = & \map(\flip(\tup)(g(v)))(\map(f)(\cons(a,x))) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \zipPad(f(u),g(v))(\map(f)(\cons(a,x)),\nil) \\
 & = & \zipPad(f(u),g(v))(\map(f)(\cons(a,x)),y)
\end{eqnarray*}$$
as needed. If $y = \cons(b,w)$, we have
$$\begin{eqnarray*}
 &   & \map(\tPair(f,g))(\zipPad(u,v)(\cons(a,x),\cons(b,w))) \\
 & = & \map(\tPair(f,g))(\cons((a,b),\zipPad(u,v)(x,w))) \\
 & = & \cons(\tPair(f,g)(a,b),\map(\tPair(f,g))(\zipPad(u,v)(x,w))) \\
 & = & \cons((f(a),g(b)),\zipPad(f(u),g(v))(\map(f)(x),\map(g)(w))) \\
 & = & \zipPad(f(u),g(v))(\cons(f(a),\map(f)(x)),\cons(g(b),\map(g)(w))) \\
 & = & \zipPad(f(u),g(v))(\map(f)(\cons(a,x)),\map(g)(\cons(b,w))) \\
 & = & \zipPad(f(u),g(v))(\map(f)(\cons(a,x)),\map(g)(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_zipPad_tpair :: (List t, Equal (t (Pair a b)))
>   => t a -> t b -> Test ((a -> a) -> (b -> b) -> a -> b -> t a -> t b -> Bool)
> _test_zipPad_tpair _ _ =
>   testName "map(tpair(f,g))(zipPad(u,v)(x,y)) == zipPad(f(u),g(v))(map(f)(x),map(g)(y))" $
>   \f g u v x y -> eq
>     (map (tpair f g) (zipPad u v x y))
>     (zipPad (f u) (g v) (map f x) (map g y))

::::::::::::::::::::
::::::::::::::::::::

$\zipPad$ interacts with $\length$.

:::::: theorem :::::
[]{#thm-zippad-length}
Let $A$ and $B$ be sets, with $u \in A$, $v \in B$, $x \in \lists{A}$, and $y \in \lists{B}$. Then $$\length(\zipPad(u,v)(x,y)) = \nmax(\length(x),\length(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zipPad(u,v)(x,y)) \\
 & = & \length(\zipPad(u,v)(\nil,y)) \\
 &     \href{@zippad@#cor-zippad-nil-left}
   = & \length(\map(\tup(u))(y)) \\
 &     \href{@map@#thm-length-map}
   = & \length(y) \\
 &     \href{@max-min@#thm-max-zero-left}
   = & \nmax(\zero,\length(y)) \\
 & = & \nmax(\length(\nil),\length(y)) \\
 & = & \nmax(\length(x),\length(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. We consider two possibilities for $y$: either $y = \nil$ or $y = \cons(b,w)$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\zipPad(u,v)(\cons(a,x),y)) \\
 & = & \length(\zipPad(u,v)(\cons(a,x),\nil)) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \length(\map(\flip(\tup)(v))(\cons(a,x))) \\
 &     \href{@map@#thm-length-map}
   = & \length(\cons(a,x)) \\
 & = & \nmax(\length(\cons(a,x)),\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \nmax(\length(\cons(a,x)),\length(\nil)) \\
 & = & \nmax(\length(\cons(a,x)),\length(y))
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,w)$. Now
$$\begin{eqnarray*}
 &   & \length(\zipPad(u,v)(\cons(a,x),y)) \\
 & = & \length(\zipPad(u,v)(\cons(a,x),\cons(b,w))) \\
 & = & \length(\cons((a,b),\zipPad(u,v)(x,w))) \\
 & = & \next(\length(\zipPad(u,v)(x,w))) \\
 &     \href{@zippad@#thm-zippad-length}
   = & \next(\nmax(\length(x),\length(w))) \\
 &     \href{@max-min@#thm-next-max-distribute}
   = & \nmax(\next(\length(x)),\next(\length(w))) \\
 & = & \nmax(\length(\cons(a,x)),\length(\cons(b,w))) \\
 & = & \nmax(\length(\cons(a,x)),\length(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_zipPad_length :: (List t, Natural n, Equal n)
>   => t a -> t b -> n -> Test (a -> b -> t a -> t b -> Bool)
> _test_zipPad_length _ _ n =
>   testName "length(zipPad(u,v)(x,y)) == max(length(x),length(y))" $
>   \u v x y -> eq
>     ((length (zipPad u v x y)) `withTypeOf` n)
>     (max (length x) (length y))

::::::::::::::::::::
::::::::::::::::::::

$\zipPad$ is also kind of associative:

:::::: theorem :::::
[]{#thm-zippad-assocL}[]{#thm-zippad-assocR}
Let $A$, $B$, and $C$ be sets, with $u \in A$, $v \in B$, $w \in C$, $x \in \lists{A}$, $y \in \lists{B}$, and $z \in \lists{C}$. Then the following hold.

1. We have
$$\begin{eqnarray*}
 &   & \zipPad((u,v),w)(\zipPad(u,v)(x,y),z) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z))).
\end{eqnarray*}$$
2. We have
$$\begin{eqnarray*}
 &   & \zipPad(u,(v,w))(x,\zipPad(v,w)(y,z)) \\
 & = & \map(\tAssocR)(\zipPad((u,v),w)(\zipPad(u,v)(x,y),z)).
\end{eqnarray*}$$

::: proof ::::::::::
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad((u,v),w)(\zipPad(u,v)(x,y),z) \\
 & = & \zipPad((u,v),w)(\zipPad(u,v)(\nil,y),z) \\
 & = & \zipPad((u,v),w)(\nil,z) \\
 & = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\tAssocL)(\nil) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\nil,\zipPad(v,w)(y,z))) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad((u,v),w)(\zipPad(u,v)(\cons(a,x),y),z) \\
 & = & \zipPad((u,v),w)(\zipPad(u,v)(\cons(a,x),\nil),z) \\
 & = & \zipPad((u,v),w)(\nil,z) \\
 & = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\tAssocL)(\nil) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\nil)) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\zipPad(v,w)(\nil,z))) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\zipPad(v,w)(y,z)))
\end{eqnarray*}$$
as claimed. Similarly, if $z = \nil$, we have
$$\begin{eqnarray*}
 &   & \zipPad(\tup(u)(v),w)(\zipPad(u,v)(\cons(a,x),y),z) \\
 &     \let{z = \nil}
   = & \zipPad(\tup(u)(v),w)(\zipPad(u,v)(\cons(a,x),y),\nil) \\
 &     \href{@zippad@#thm-zippad-nil-right}
   = & \map(\flip(\tup)(w))(\zipPad(u,v)(\cons(a,x),y)) \\
 & = & (@@@)
\end{eqnarray*}$$
as claimed. Suppose then that $y = \cons(b,u)$ and $z = \cons(c,v)$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \zipPad((u,v),w)(\zipPad(u,v)(\cons(a,x),y),z) \\
 & = & \zipPad((u,v),w)(\zipPad(u,v)(\cons(a,x),\cons(b,u)),\cons(c,v)) \\
 & = & \zipPad((u,v),w)(\cons((a,b),\zipPad(u,v)(x,u)),\cons(c,v)) \\
 & = & \cons(((a,b),c),\zipPad((u,v),w)(\zipPad(u,v)(x,u),v)) \\
 & = & \cons(\tAssocL(a,(b,c)),\map(\tAssocL)(\zipPad(u,(v,w))(x,\zipPad(v,w)(u,v)))) \\
 & = & \map(\tAssocL)(\cons((a,(b,c)),\zipPad(u,(v,w))(x,\zipPad(v,w)(u,v)))) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\cons((b,c),\zipPad(v,w)(u,v)))) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\zipPad(v,w)(\cons(b,u),\cons(c,v)))) \\
 & = & \map(\tAssocL)(\zipPad(u,(v,w))(\cons(a,x),\zip(y,z)))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \zipPad(u,(v,w))(x,\zipPad(v,w)(y,z)) \\
 & = & \id(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z))) \\
 & = & \map(\id)(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z))) \\
 & = & \map(\compose(\tAssocR)(\tAssocL))(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z))) \\
 & = & \map(\tAssocR)(\map(\tAssocL)(\zipPad(u,(v,w))(x,\zipPad(v,w)(y,z)))) \\
 & = & \map(\tAssocR)(\zipPad((u,v),w)(\zipPad(u,v)(x,y),z))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_zipPad_zipPad_left :: (List t, Equal a, Equal (t (Pair (Pair a a) a)))
>   => t a -> Test (a -> a -> a -> t a -> t a -> t a -> Bool)
> _test_zipPad_zipPad_left _ =
>   testName "zipPad((a,b),c)(zipPad(a,b)(x,y),z) == map(tassocL)zipPad(a,(b,c))(x,zipPad(b,c)(y,z))" $
>   \a b c x y z -> eq
>     (zipPad (tup a b) c (zipPad a b x y) z)
>     (map tassocL (zipPad a (tup b c) x (zipPad b c y z)))
> 
> 
> _test_zipPad_zipPad_right :: (List t, Equal a, Equal (t (Pair a (Pair a a))))
>   => t a -> Test (a -> a -> a -> t a -> t a -> t a -> Bool)
> _test_zipPad_zipPad_right _ =
>   testName "zipPad((a,b),c)(zipPad(a,b)(x,y),z) == map(tassocR)zipPad(a,(b,c))(x,zipPad(b,c)(y,z))" $
>   \a b c x y z -> eq
>     (zipPad a (tup b c) x (zipPad b c y z))
>     (map tassocR (zipPad (tup a b) c (zipPad a b x y) z))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_zipPad ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName b, Equal b, Show b, Arbitrary b, CoArbitrary b
>   , TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , TypeName (t a), TypeName (t b), List t, Equal (t a), Show (t a), Arbitrary (t a)
>   , Equal (t b), Show (t b), Arbitrary (t b), Equal (t (Pair a b)), Equal (t (Pair b a))
>   , Equal (t (Pair a (Pair a a))), Equal (t (Pair (Pair a a) a))
>   ) => Int -> Int -> t a -> t b -> n -> IO ()
> _test_zipPad size cases t u n = do
>   testLabel3 "zipPad" t u n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_zipPad_nil_list t u)
>   runTest args (_test_zipPad_cons_nil t u)
>   runTest args (_test_zipPad_cons_cons t u)
>   runTest args (_test_zipPad_nil_right t u)
>   runTest args (_test_zipPad_tswap t u)
>   runTest args (_test_zipPad_tpair t u)
>   runTest args (_test_zipPad_length t u n)
>   runTest args (_test_zipPad_zipPad_left t)
>   runTest args (_test_zipPad_zipPad_right t)

Main:

> main_zipPad :: IO ()
> main_zipPad = do
>   _test_zipPad 20 100 (nil :: ConsList Bool)  (nil :: ConsList Bool)  (zero :: Unary)
>   _test_zipPad 20 100 (nil :: ConsList Unary) (nil :: ConsList Unary) (zero :: Unary)
