---
title: Tuples
author: nbloomf
date: 2014-04-02
tags: arithmetic-made-difficult, literate-haskell
slug: tuples
---

> {-# LANGUAGE NoImplicitPrelude, FlexibleContexts #-}
> module Tuples
>   ( Pair(Pair,fst,snd), dup, tup, tswap, tpair, tassocL, tassocR
>   , uncurry, curry, _test_tuple, main_tuple
>   ) where
> 
> import Testing
> import Functions
> import Flip
> import Clone
> import Composition
> import Booleans
> import And

Today we'll establish a few basic utility functions on *tuples*. First, recall some definitions.

:::::: definition ::
[]{#def-dup}[]{#def-fst-dup}[]{#def-snd-dup}
Let $A$ and $B$ be sets. There is a set $A \times B$ together with two functions $\fst : A \times B \rightarrow A$ and $\snd : A \times B \rightarrow B$ having the property that if $X$ is a set and $\sigma : X \rightarrow A$ and $\tau : X \rightarrow B$ functions then there is a unique map $\Theta : X \rightarrow A \times B$ such that $\fst \circ \Theta = \sigma$ and $\snd \circ \Theta = \tau$. That is, there is a unique $\Theta$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
X @= X @= X \\
@V{\sigma}VV @VV{\Theta}V @VV{\tau}V \\
A @<<{\fst}< A \times B @>>{\snd}> B
\end{CD}$$

We will denote this unique $\Theta : X \rightarrow A \times B$ by $\dup(\sigma,\tau)$.

More concretely, if $f : X \rightarrow A \times B$ such that $\fst(f(x)) = \sigma(x)$ and $\snd(f(x)) = \tau(x)$ for all $x \in X$, then $f = \dup(\sigma,\tau)$.
::::::::::::::::::::

Now $A \times B$ uniquely represents all possible pairs of elements of $A$ and $B$ in a precise sense.

:::::: theorem :::::
[]{#def-tup}[]{#thm-fst-tup}[]{#thm-snd-tup}
Let $A$ and $B$ be sets. Given $a \in A$ and $b \in B$, we define $\tup : A \rightarrow B \rightarrow A \times B$ by $$\tup(a)(b) = \dup(\const(a),\const(b))(\ast).$$ Now we have the following.

1. $\fst(\tup(a)(b)) = a$ and $\snd(\tup(a)(b)) = b$.
2. If $w \in A \times B$ such that $\fst(w) = a$ and $\snd(w) = b$, then $w = \tup(a)(b)$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \fst(\tup(a)(b)) \\
 &     \href{@tuples@#def-tup}
   = & \fst(\dup(\const(a),\const(b))(\ast)) \\
 &     \href{@tuples@#def-fst-dup}
   = & \const(a)(\ast) \\
 &     \href{@functions@#def-const}
   = & a
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\tup(a)(b)) \\
 &     \href{@tuples@#def-tup}
   = & \snd(\dup(\const(a),\const(b))(\ast)) \\
 &     \href{@tuples@#def-snd-dup}
   = & \const(b)(\ast) \\
 &     \href{@functions@#def-const}
   = & b
\end{eqnarray*}$$
as claimed.
2. Suppose $\fst(w) = a$ and $\snd(w) = b$, and consider $\const(w)$ as a function $\ast \rightarrow A \times B$. Note that
$$\begin{eqnarray*}
 &   & \fst(\const(w)(\ast)) \\
 &     \href{@functions@#def-const}
   = & \fst(w) \\
 &     \hyp{\fst(w) = a}
   = & a \\
 &     \href{@functions@#def-const}
   = & \const(a)(\ast)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\const(w)(\ast)) \\
 &     \href{@functions@#def-const}
   = & \snd(w) \\
 &     \hyp{\snd(w) = b}
   = & b \\
 &     \href{@functions@#def-const}
   = & \const(b)(\ast)
\end{eqnarray*}$$
so by the universal property of $A \times B$, $w = \tup(a)(b)$.
::::::::::::::::::::
::::::::::::::::::::

In Haskell we can model $A \times B$, and the maps in the universal property, with the following type.

> data Pair a b = Pair
>   { fst :: a
>   , snd :: b
>   } deriving Show
> 
> dup :: (x -> a) -> (x -> b) -> x -> Pair a b
> dup f g x = Pair (f x) (g x)
> 
> tup :: a -> b -> Pair a b
> tup a b = dup (const a) (const b) undefined
> 
> instance (Equal a, Equal b) => Equal (Pair a b) where
>   eq a b = and (eq (fst a) (fst b)) (eq (snd a) (snd b))
> 
> instance (Arbitrary a, Arbitrary b) => Arbitrary (Pair a b) where
>   arbitrary = do
>     a <- arbitrary
>     b <- arbitrary
>     return (Pair a b)
> 
> instance (CoArbitrary a, CoArbitrary b) => CoArbitrary (Pair a b) where
>   coarbitrary (Pair a b) = coarbitrary a . coarbitrary b
> 
> instance (TypeName a, TypeName b) => TypeName (Pair a b) where
>   typeName (Pair a b) = "Pair " ++ typeName a ++ " " ++ typeName b

$\dup$ is a $\tup$.

:::::: theorem :::::
Let $A$ and $B$ be sets. For all $x \in A \times B$ we have $$\dup(f,g)(x) = \tup(f(x))(g(x)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \fst(\dup(f,g)(x)) \\
 &     \href{@tuples@#def-fst-dup}
   = & f(x)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\dup(f,g)(x)) \\
 &     \href{@tuples@#def-snd-dup}
   = & g(x)
\end{eqnarray*}$$
so that $\dup(f,g)(x) = \tup(f(x))(g(x))$ by the uniqueness of $\tup$.
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_dup_tup :: (Equal a, Equal b)
>   => a -> b -> Test ((Pair a b -> a) -> (Pair a b -> b) -> Pair a b -> Bool)
> _test_dup_tup _ _ =
>   testName "dup(f,g)(x) == tup(f(x))(f(x))" $
>   \f g x -> eq (dup f g x) (tup (f x) (g x))

::::::::::::::::::::
::::::::::::::::::::

For example, $\id_{A \times B}$ is a $\dup$.

:::::: theorem :::::
[]{#thm-dup-fst-snd}
Provided the types match up, we have $$\dup(\fst,\snd) = \id_{A \times B}.$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \fst(\dup(\fst,\snd)(\tup(a)(b))) \\
 &     \href{@tuples@#def-fst-dup}
   = & \fst(\tup(a)(b)) \\
 &     \href{@tuples@#thm-fst-tup}
   = & a
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\dup(\fst,\snd)(\tup(a)(b))) \\
 &     \href{@tuples@#def-snd-dup}
   = & \snd(\tup(a)(b)) \\
 &     \href{@tuples@#thm-snd-tup}
   = & b
\end{eqnarray*}$$
so that $\dup(\fst,\snd)(\tup(a)(b)) = \tup(a)(b)$ for all $a \in A$ and $b \in B$.
::::::::::::::::::::

::: test :::::::::::

> _test_dup_fst_snd :: (Equal a, Equal b)
>   => a -> b -> Test (Pair a b -> Bool)
> _test_dup_fst_snd _ _ =
>   testName "dup(fst,snd) == id" $
>   \x -> eq (dup fst snd x) x

::::::::::::::::::::
::::::::::::::::::::

We define $\tSwap$ on tuples like so.

:::::: definition ::
[]{#def-tSwap}
Let $A$ and $B$ be sets. We define $\tSwap : A \times B \rightarrow B \times A$ by $$\tSwap = \dup(\snd,\fst).$$

In Haskell,

> tswap :: Pair a b -> Pair b a
> tswap = dup snd fst

::::::::::::::::::::

Elements of $A \times B$ act like "ordered pairs", and $\tSwap$ effectively reverses the order of the pair.

:::::: theorem :::::
[]{#thm-tSwap-swap}[]{#thm-tSwap-involution}
Let $A$ and $B$ be sets. Then we have the following.

1. $\tSwap(\tup(a)(b)) = \tup(b)(a)$.
2. $\tSwap(\tSwap(\tup(a)(b))) = \tup(a)(b)$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \fst(\tSwap(\tup(a)(b))) \\
 &     \href{@tuples@#def-tSwap}
   = & \fst(\dup(\snd,\fst)(\tup(a)(b))) \\
 &     \href{@tuples@#def-fst-dup}
   = & \snd(\tup(a)(b)) \\
 &     \href{@tuples@#thm-snd-tup}
   = & b
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\tSwap(\tup(a)(b))) \\
 &     \href{@tuples@#def-tSwap}
   = & \snd(\dup(\snd,\fst)(\tup(a)(b))) \\
 &     \href{@tuples@#def-snd-dup}
   = & \fst(\tup(a)(b)) \\
 &     \href{@tuples@#thm-fst-tup}
   = & a
\end{eqnarray*}$$
so that $\tSwap(\tup(a)(b)) = \tup(b)(a)$ as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tSwap(\tSwap(\tup(a)(b))) \\
 &     \href{@tuples@#thm-tSwap-swap}
   = & \tSwap(\tup(b)(a)) \\
 &     \href{@tuples@#thm-tSwap-swap}
   = & \tup(a)(b)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tswap_entries :: (Equal a, Equal b)
>   => a -> b -> Test (Pair a b -> Bool)
> _test_tswap_entries _ _ =
>   testName "tswap(tup(a)(b)) == tup(b)(a)" $
>   \(Pair a b) -> eq (tswap (tup a b)) (tup b a)
> 
> 
> _test_tswap_tswap :: (Equal a, Equal b)
>   => a -> b -> Test (Pair a b -> Bool)
> _test_tswap_tswap _ _ =
>   testName "tswap(tswap(x)) == x" $
>   \x -> eq (tswap (tswap x)) x

::::::::::::::::::::
::::::::::::::::::::

Next, the utility $\tPair$ facilitates defining functions from one tuple to another.

:::::: definition ::
[]{#def-tPair}
Let $A$, $B$, $U$, and $V$ be sets. We define $\tPair : U^A \times V^B \rightarrow (U \times V)^{A \times B}$ by $$\tPair(f,g) = \dup(\compose(f)(\fst),\compose(g)(\snd)).$$

In Haskell:

> tpair :: (a -> u) -> (b -> v) -> Pair a b -> Pair u v
> tpair f g = dup (compose f fst) (compose g snd)

::::::::::::::::::::

$\tPair$ has some nice properties.

:::::: theorem :::::
[]{#thm-tPair-tup}[]{#thm-tPair-compose}
For all $f$, $g$, $h$, $k$, $a$, and $b$ we have the following.

1. $\tPair(f,g)(\tup(a)(b)) = \tup(f(a))(g(b))$.
2. $\compose(\tPair(f,g))(\tPair(h,k)) = \tPair(\compose(f)(h),\compose(g)(k))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \tPair(f,g)(\tup(a)(b)) \\
 &     \href{@tuples@#def-tPair}
   = & \dup(\compose(f)(\fst))(\compose(g)(\snd))(\tup(a)(b)) \\
 &     \href{@tuples@#thm-dup-tup}
   = & \tup(\compose(f)(\fst)(\tup(a)(b)))(\compose(g)(\snd)(\tup(a)(b))) \\
 &     \href{@functions@#def-compose}
   = & \tup(f(\fst(\tup(a)(b))))(\compose(g)(\snd)(\tup(a)(b))) \\
 &     \href{@functions@#def-compose}
   = & \tup(f(\fst(\tup(a)(b))))(g(\snd(\tup(a)(b)))) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(f(a))(g(\snd(\tup(a)(b)))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(f(a))(g(b))
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \compose(\tPair(f,g))(\tPair(h,k))(\tup(a)(b)) \\
 &     \href{@functions@#def-compose}
   = & \tPair(f,g)(\tPair(h,k)(\tup(a)(b))) \\
 &     \href{@tuples@#thm-tPair-tup}
   = & \tPair(f,g)(\tup(h(a))(k(b))) \\
 &     \href{@tuples@#thm-tPair-tup}
   = & \tup(f(h(a)))(g(k(b))) \\
 &     \href{@functions@#def-compose}
   = & \tup(f(h(a)))(\compose(g)(k)(b)) \\
 &     \href{@functions@#def-compose}
   = & \tup(\compose(f)(h)(a))(\compose(g)(k)(b)) \\
 &     \href{@tuples@#thm-tPair-tup}
   = & \tPair(\compose(f)(h),\compose(g)(k))(\tup(a)(b))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tpair_apply :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> Pair a b -> Bool)
> _test_tpair_apply _ _ =
>   testName "tpair(f,g)(tup(a)(b)) == tup(f(a))(g(b))" $
>   \f g (Pair a b) -> eq (tpair f g (tup a b)) (tup (f a) (g b))
> 
> 
> _test_tpair_tpair :: (Equal a, Equal b)
>   => a -> b
>   -> Test ((a -> a) -> (b -> b) -> (a -> a) -> (b -> b) -> Pair a b -> Bool)
> _test_tpair_tpair _ _ =
>   testName "tpair(f,g) . tpair(h,k) == tpair(f . h, g . k)" $
>   \f g h k x ->
>     eq
>       (tpair f g (tpair h k x))
>       (tpair (compose f h) (compose g k) x)

::::::::::::::::::::
::::::::::::::::::::

Finally, note that although as sets $A \times (B \times C)$ and $(A \times B) \times C$ cannot possibly be equal to each other in general, they are naturally isomorphic via $\tAssocL$ and $\tAssocR$.

:::::: definition ::
[]{#def-tAssocL}[]{#def-tAssocR}
Let $A$, $B$, and $C$ be sets. We define $\tAssocL : A \times (B \times C) \rightarrow (A \times B) \times C$ by $$\tAssocL = \dup(\dup(\fst,\compose(\fst)(\snd)),\compose(\snd)(\snd))$$ and define $\tAssocR : (A \times B) \times C \rightarrow A \times (B \times C)$ by $$\tAssocR = \dup(\compose(\fst)(\fst),\dup(\compose(\snd)(\fst),\snd)).$$

In Haskell:

> tassocL :: Pair a (Pair b c) -> Pair (Pair a b) c
> tassocL = dup (dup fst (compose fst snd)) (compose snd snd)
> 
> tassocR :: Pair (Pair a b) c -> Pair a (Pair b c)
> tassocR = dup (compose fst fst) (dup (compose snd fst) snd)

::::::::::::::::::::

Now $\tAssocL$ and $\tAssocR$ have some nice properties.

:::::: theorem :::::
[]{#thm-tAssocL-tup}[]{#thm-tAssocR-tup}[]{#thm-tAssocR-tAssocL}[]{#thm-tAssocL-tAssocR}
The following hold whenever everything has the appropriate type.

1. $\tAssocL(\tup(a)(\tup(b)(c))) = \tup(\tup(a)(b))(c)$.
2. $\tAssocR(\tup(\tup(a)(b))(c)) = \tup(a)(\tup(b)(c))$.
3. $\compose(\tAssocR)(\tAssocL) = \id$.
4. $\compose(\tAssocL)(\tAssocR) = \id$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \tAssocL(\tup(a)(\tup(b)(c))) \\
 &     \href{@tuples@#def-tAssocL}
   = & \dup(\dup(\fst,\compose(\fst)(\snd)),\compose(\snd)(\snd))(\tup(a)(\tup(b)(c))) \\
 &     \href{@tuples@#thm-dup-tup}
   = & \tup(\dup(\fst,\compose(\fst)(\snd))(\tup(a)(\tup(b)(c))))(\compose(\snd)(\snd)(\tup(a)(\tup(b)(c)))) \\
 &     \href{@functions@#def-compose}
   = & \tup(\dup(\fst,\compose(\fst)(\snd))(\tup(a)(\tup(b)(c))))(\snd(\snd(\tup(a)(\tup(b)(c))))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(\dup(\fst,\compose(\fst)(\snd))(\tup(a)(\tup(b)(c))))(\snd(\tup(b)(c))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(\dup(\fst,\compose(\fst)(\snd))(\tup(a)(\tup(b)(c))))(c) \\
 &     \href{@tuples@#thm-dup-tup}
   = & \tup(\tup(\fst(\tup(a)(\tup(b)(c))))(\compose(\fst)(\snd)(\tup(a)(\tup(b)(c)))))(c) \\
 &     \href{@functions@#def-compose}
   = & \tup(\tup(\fst(\tup(a)(\tup(b)(c))))(\fst(\snd(\tup(a)(\tup(b)(c))))))(c) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(\tup(\fst(\tup(a)(\tup(b)(c))))(\fst(\tup(b)(c))))(c) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(\tup(\fst(\tup(a)(\tup(b)(c))))(b))(c) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(\tup(a)(b))(c)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tAssocR(\tup(\tup(a)(b))(c)) \\
 &     \href{@tuples@#def-tAssocR}
   = & \dup(\compose(\fst)(\fst),\dup(\compose(\snd)(\fst),\snd))(\tup(\tup(a)(b))(c)) \\
 &     \href{@tuples@#thm-dup-tup}
   = & \tup(\compose(\fst)(\fst)(\tup(\tup(a)(b))(c)))(\dup(\compose(\snd)(\fst),\snd)(\tup(\tup(a)(b))(c))) \\
 &     \href{@functions@#def-compose}
   = & \tup(\fst(\fst(\tup(\tup(a)(b))(c))))(\dup(\compose(\snd)(\fst),\snd)(\tup(\tup(a)(b))(c))) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(\fst(\tup(a)(b)))(\dup(\compose(\snd)(\fst),\snd)(\tup(\tup(a)(b))(c))) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(a)(\dup(\compose(\snd)(\fst),\snd)(\tup(\tup(a)(b))(c))) \\
 &     \href{@tuples@#thm-dup-tup}
   = & \tup(a)(\tup(\compose(\snd)(\fst)(\tup(\tup(a)(b))(c)))(\snd(\tup(\tup(a)(b))(c)))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(a)(\tup(\compose(\snd)(\fst)(\tup(\tup(a)(b))(c)))(c)) \\
 &     \href{@functions@#def-compose}
   = & \tup(a)(\tup(\snd(\fst(\tup(\tup(a)(b))(c))))(c)) \\
 &     \href{@tuples@#thm-fst-tup}
   = & \tup(a)(\tup(\snd(\tup(a)(b)))(c)) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(a)(\tup(b)(c))
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \compose(\tAssocR)(\tAssocL)(\tup(a)(\tup(b)(c))) \\
 &     \href{@functions@#def-compose}
   = & \tAssocR(\tAssocL(\tup(a)(\tup(b)(c)))) \\
 &     \href{@tuples@#thm-tAssocL-tup}
   = & \tAssocR(\tup(\tup(a)(b))(c)) \\
 &     \href{@tuples@#thm-tAssocR-tup}
   = & \tup(a)(\tup(b)(c))
\end{eqnarray*}$$
as claimed.
4. Note that
$$\begin{eqnarray*}
 &   & \compose(\tAssocL)(\tAssocR)(\tup(\tup(a)(b))(c)) \\
 &     \href{@functions@#def-compose}
   = & \tAssocL(\tAssocR(\tup(\tup(a)(b))(c))) \\
 &     \href{@tuples@#thm-tAssocR-tup}
   = & \tAssocL(\tup(a)(\tup(b)(c))) \\
 &     \href{@tuples@#thm-tAssocL-tup}
   = & \tup(\tup(a)(b))(c)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tassocL_entries :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> b -> c -> Bool)
> _test_tassocL_entries _ _ _ =
>   testName "tassocL(tup(a)(tup(b)(c))) == tup(tup(a)(b))(c)" $
>   \a b c -> eq (tassocL (tup a (tup b c))) (tup (tup a b) c)
> 
> 
> _test_tassocR_entries :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> b -> c -> Bool)
> _test_tassocR_entries _ _ _ =
>   testName "tassocR(tup(tup(a)(b))(c)) == tup(a)(tup(b)(c))" $
>   \a b c -> eq (tassocR (tup (tup a b) c)) (tup a (tup b c))
> 
> 
> _test_tassocL_tassocR :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (Pair (Pair a b) c -> Bool)
> _test_tassocL_tassocR _ _ _ =
>   testName "compose(tassocL)(tassocR) == id" $
>   \x -> eq (tassocL (tassocR x)) x
> 
> 
> _test_tassocR_tassocL :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (Pair a (Pair b c) -> Bool)
> _test_tassocR_tassocL _ _ _ =
>   testName "compare(tassocR)(tassocL) == id" $
>   \x -> eq (tassocR (tassocL x)) x

::::::::::::::::::::
::::::::::::::::::::

Higher-order functions can be converted to functions on tuples (and back).

:::::: definition ::
[]{#def-uncurry}[]{#def-curry}
Let $A$, $B$, and $C$ be sets. If $f : A \rightarrow B \rightarrow C$, we define $\uncurry(f) : A \times B \rightarrow C$ by $$\uncurry(f)(\tup(a)(b)) = f(a)(b).$$ If $g : A \times B \rightarrow C$, we define $\curry(g) : A \rightarrow B \rightarrow C$ by $$\curry(g)(a)(b) = g(\tup(a)(b)).$$

In Haskell:

> uncurry :: (a -> b -> c) -> Pair a b -> c
> uncurry f (Pair a b) = f a b
> 
> curry :: (Pair a b -> c) -> a -> b -> c
> curry g a b = g (tup a b)

::::::::::::::::::::


Testing
-------

Suite:

> _test_tuple
>   :: ( Equal a, Show a, Arbitrary a, CoArbitrary a, TypeName a
>      , Equal b, Show b, Arbitrary b, CoArbitrary b, TypeName b
>      , Equal c, Show c, Arbitrary c, CoArbitrary c, TypeName c
>   ) => Int -> Int -> a -> b -> c -> IO ()
> _test_tuple size cases a b c = do
>   testLabel3 "Tuple" a b c
>   let args = testArgs size cases
> 
>   runTest args (_test_dup_fst_snd a b)
>   runTest args (_test_dup_tup a b)
>   runTest args (_test_tswap_entries a b)
>   runTest args (_test_tswap_tswap a b)
>   runTest args (_test_tpair_apply a b)
>   runTest args (_test_tpair_tpair a b)
>   runTest args (_test_tassocL_entries a b c)
>   runTest args (_test_tassocR_entries a b c)
>   runTest args (_test_tassocL_tassocR a b c)
>   runTest args (_test_tassocR_tassocL a b c)

Main:

> main_tuple :: IO ()
> main_tuple = do
>   _test_tuple 20 100 (true :: Bool) (true :: Bool) (true :: Bool)
> 
>   let a = tup true true :: Pair Bool Bool
> 
>   _test_functions 20 100 a a a a
>   _test_flip      20 100 a a a a a a a
>   _test_clone     20 100 a a
>   _test_compose   20 100 a a a a a a a
