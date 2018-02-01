---
title: Tuples
author: nbloomf
date: 2014-04-02
tags: arithmetic-made-difficult, literate-haskell
slug: tuples
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Tuples
>   ( Pair(Pair,fst,snd), dup, tup, tswap, tpair, tassocL, tassocR, tupL, tupR, uncurry
>   , _test_tuple, main_tuple
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Functions

Today we'll establish a few basic utility functions on *tuples*. First, recall some definitions.

:::::: definition ::
[]{#def-fst-dup}[]{#def-snd-dup}
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
 & = & \fst(\dup(\const(a),\const(b))(\ast)) \\
 & = & \const(a)(\ast) \\
 & = & a
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\tup(a)(b)) \\
 & = & \snd(\dup(\const(a),\const(b))(\ast)) \\
 & = & \const(b)(\ast) \\
 & = & b
\end{eqnarray*}$$
as claimed.
2. Define $\omega : \ast \rightarrow A \times B$ by $\omega = \const(w)$. Now
$$\begin{eqnarray*}
 &   & \fst(\omega(\ast)) \\
 & = & \fst(w) \\
 & = & a \\
 & = & \const(a)(\ast)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\omega(\ast)) \\
 & = & \snd(w) \\
 & = & b \\
 & = & \const(b)(\ast)
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

For example, $\id_{A \times B}$ is a $\dup$.

:::::: theorem :::::
[]{#thm-dup-fst-snd}
Provided the types match up, we have $$\dup(\fst,\snd) = \id_{A \times B}.$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \fst(\dup(\fst,\snd)(\tup(a)(b))) \\
 & = & \fst(\tup(a)(b)) \\
 & = & a
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\dup(\fst,\snd)(\tup(a)(b))) \\
 & = & \snd(\tup(a)(b)) \\
 & = & b
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
[]{#def-tswap}
Let $A$ and $B$ be sets. We define $\tSwap : A \times B \rightarrow B \times A$ by $$\tSwap = \dup(\snd,\fst).$$

In Haskell,

> tswap :: Pair a b -> Pair b a
> tswap = dup snd fst

::::::::::::::::::::

Elements of $A \times B$ act like "ordered pairs", and $\tSwap$ effectively reverses the order of the pair.

:::::: theorem :::::
[]{#thm-tswap-swap}[]{#thm-tswap-involution}
Let $A$ and $B$ be sets. Then we have the following.

1. $\tSwap(\tup(a)(b)) = \tup(b)(a)$.
2. $\tSwap(\tSwap(\tup(a)(b))) = \tup(a)(b)$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \fst(\tSwap(\tup(a)(b))) \\
 & = & \fst(\dup(\snd,\fst)(\tup(a)(b))) \\
 & = & \snd(\tup(a)(b)) \\
 & = & b
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(\tSwap(\tup(a)(b))) \\
 & = & \snd(\dup(\snd,\fst)(\tup(a)(b))) \\
 & = & \fst(\tup(a)(b)) \\
 & = & a
\end{eqnarray*}$$
so that $\tSwap(\tup(a)(b)) = \tup(b)(a)$ as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tSwap(\tSwap(\tup(a)(b))) \\
 & = & \tSwap(\tup(b)(a)) \\
 & = & \tup(a)(b)
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
Let $A$, $B$, $U$, and $V$ be sets. We define $\tPair : U^A \times V^B \rightarrow (U \times V)^{A \times B}$ by $$\tPair(f,g) = \dup(f \circ \fst, g \circ \snd).$$

In Haskell:

> tpair :: (a -> u) -> (b -> v) -> Pair a b -> Pair u v
> tpair f g = dup (compose f fst) (compose g snd)

::::::::::::::::::::

$\tPair$ has some nice properties.

:::::: theorem :::::
For all $f$, $g$, $h$, $k$, $a$, and $b$ we have the following.

1. $\tPair(f,g)(\tup(a)(b)) = \tup(f(a))(g(b))$.
2. $\compose(\tPair(f,g))(\tPair(h,k)) = \tPair(\compose(f)(h),\compose(g)(k))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \tPair(f,g)(a,b) \\
 & = & \dup(f \circ \fst, g \circ \snd)(a,b) \\
 & = & ((f \circ \fst)(a,b),(g \circ \snd)(a,b)) \\
 & = & (f(\fst(a,b)),g(\snd(a,b))) \\
 & = & (f(a),g(b))
\end{eqnarray*}$$
as claimed.
2. Note that for all $(a,b)$ we have
$$\begin{eqnarray*}
 &   & (\tPair(f,g) \circ \tPair(h,k))(a,b) \\
 & = & \tPair(f,g)(\tPair(h,k)(a,b)) \\
 & = & \tPair(f,g)(h(a),k(b)) \\
 & = & (f(h(a)),g(k(b))) \\
 & = & ((f \circ h)(a),(g \circ k)(b)) \\
 & = & \tPair(f \circ h, g \circ k)(a,b)
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
Let $A$, $B$, and $C$ be sets. We define $\tAssocL : A \times (B \times C) \rightarrow (A \times B) \times C$ by $$\tAssocL = \dup(\dup(\fst, \fst \circ \snd), \snd \circ \snd)$$ and define $\tAssocR : (A \times B) \times C \rightarrow A \times (B \times C)$ by $$\tAssocR = \dup(\fst \circ \fst, \dup(\snd \circ \fst, \snd)).$$

In Haskell:

> tassocL :: Pair a (Pair b c) -> Pair (Pair a b) c
> tassocL = dup (dup fst (compose fst snd)) (compose snd snd)
> 
> tassocR :: Pair (Pair a b) c -> Pair a (Pair b c)
> tassocR = dup (compose fst fst) (dup (compose snd fst) snd)

::::::::::::::::::::

Now $\tAssocL$ and $\tAssocR$ have some nice properties.

:::::: theorem :::::
The following hold whenever everything has the appropriate type.

1. $\tAssocL(a,(b,c)) = ((a,b),c)$.
2. $\tAssocR((a,b),c) = (a,(b,c))$.
3. $\tAssocR \circ \tAssocL = \id$.
4. $\tAssocL \circ \tAssocR = \id$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \tAssocL(a,(b,c)) \\
 & = & \dup(\dup(\fst, \fst \circ \snd),\snd \circ \snd)(a,(b,c)) \\
 & = & (\dup(\fst,\fst \circ \snd)(a,(b,c)),(\snd \circ \snd)(a,(b,c))) \\
 & = & ((\fst(a,(b,c)),\fst(\snd(a,(b,c)))),\snd(\snd(a,(b,c)))) \\
 & = & ((a,\fst(b,c)),\snd(b,c)) \\
 & = & ((a,b),c)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tAssocR((a,b),c) \\
 & = & \dup(\fst \circ \fst, \dup(\snd \circ \fst, \snd))((a,b),c) \\
 & = & (\fst(\fst((a,b),c)),\dup(\snd \circ \fst, \snd)((a,b),c)) \\
 & = & (\fst(a,b),(\snd(\fst((a,b),c)),\snd((a,b),c))) \\
 & = & (a,(\snd(a,b),c)) \\
 & = & (a,(b,c))
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & (\tAssocR \circ \tAssocL)(a,(b,c)) \\
 & = & \tAssocR(\tAssocL(a,(b,c))) \\
 & = & \tAssocR((a,b),c) \\
 & = & (a,(b,c))
\end{eqnarray*}$$
as claimed.
4. Note that
$$\begin{eqnarray*}
 &   & (\tAssocL \circ \tAssocR)((a,b),c) \\
 & = & \tAssocL(\tAssocR((a,b),c)) \\
 & = & \tAssocL(a,(b,c)) \\
 & = & ((a,b),c)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tassocL_entries :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> b -> c -> Bool)
> _test_tassocL_entries _ _ _ =
>   testName "tassocL(tup(a)(tup(b)(c)) == tup(tup(a)(b))(c)" $
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

We also define a pair of helper functions for constructing tuples.

:::::: definition ::
Let $A$ and $B$ be sets. We define $\tupL : A \rightarrow (A \times B)^B$ by $$\tup(a)(b) = (a,b)$$ and $\tupR : B \rightarrow (A \times B)^B$ by $$\tupR(b)(a) = (a,b).$$

In Haskell:

> tupL :: a -> b -> Pair a b
> tupL a b = tup a b
> 
> tupR :: b -> a -> Pair a b
> tupR b a = tup a b

::::::::::::::::::::

$\tupL$ and $\tupR$ interact with $\fst$ and $\snd$.

:::::: theorem :::::
Let $A$ and $B$ be sets. For all $a \in A$ and $b \in B$ we have the following.

1. $\fst(\tupL(a)(b)) = a$.
2. $\snd(\tupL(a)(b)) = b$.
3. $\fst(\tupR(b)(a)) = a$.
4. $\snd(\tupR(b)(a)) = b$.

::: proof ::::::::::
1. $\fst(\tupL(a)(b)) = \fst(a,b) = a$.
2. $\snd(\tupL(a)(b)) = \snd(a,b) = b$.
3. $\fst(\tupR(b)(a)) = \fst(a,b) = a$.
4. $\snd(\tupR(b)(a)) = \snd(a,b) = b$.
::::::::::::::::::::

::: test :::::::::::

> _test_fst_tupL :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_fst_tupL _ _ =
>   testName "fst(tupL(a)(b)) == a" $
>   \a b -> eq (fst (tupL a b)) a
> 
> 
> _test_snd_tupL :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_snd_tupL _ _ =
>   testName "snd(tupL(a)(b)) == b" $
>   \a b -> eq (snd (tupL a b)) b
> 
> 
> _test_fst_tupR :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_fst_tupR _ _ =
>   testName "fst(tupR(b)(a)) == a" $
>   \a b -> eq (fst (tupR b a)) a
> 
> 
> _test_snd_tupR :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_snd_tupR _ _ =
>   testName "snd(tupR(b)(a)) == b" $
>   \a b -> eq (snd (tupR b a)) b

::::::::::::::::::::
::::::::::::::::::::

$\tupL$ and $\tupR$ interact with $\tSwap$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $a \in A$ and $b \in B$. Then we have the following.

1. $\tSwap \circ \tupL(a) = \tupR(a)$.
2. $\tSwap \circ \tupR(b) = \tupL(b)$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & (\tSwap \circ \tupL(a))(b) \\
 & = & \tSwap(\tupL(a)(b)) \\
 & = & \tSwap(a,b) \\
 & = & (b,a) \\
 & = & \tupR(a)(b).
\end{eqnarray*}$$
2. Note that
$$\begin{eqnarray*}
 &   & (\tSwap \circ \tupR(b))(a) \\
 & = & \tSwap(\tupR(b)(a)) \\
 & = & \tSwap(a,b) \\
 & = & (b,a) \\
 & = & \tupL(b)(a).
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_tswap_tupL :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_tswap_tupL _ _ =
>   testName "tswap . tupL(a) == tupR(a)" $
>   \a b -> eq (tswap (tupL a b)) (tupR a b)
> 
> 
> _test_tswap_tupR :: (Equal a, Equal b)
>   => a -> b -> Test (a -> b -> Bool)
> _test_tswap_tupR _ _ =
>   testName "tswap . tupR(b) == tupL(b)" $
>   \a b -> eq (tswap (tupR b a)) (tupL b a)

::::::::::::::::::::
::::::::::::::::::::

$\tupL$ and $\tupR$ interact with $\tPair$.

:::::: theorem :::::
Let $f : A \rightarrow U$ and $g : B \rightarrow V$, with $a \in A$ and $b \in B$. Then we have the following.

1. $\tPair(f,g) \circ \tupL(a) = \tupL(f(a)) \circ g$.
2. $\tPair(f,g) \circ \tupR(b) = \tupR(g(b)) \circ f$.

::: proof ::::::::::
1. Let $b \in B$. Then
$$\begin{eqnarray*}
 &   & (\tPair(f,g) \circ \tupL(a))(b) \\
 & = & \tPair(f,g)(\tupL(a)(b)) \\
 & = & \tPair(f,g)(a,b) \\
 & = & (f(a),g(b)) \\
 & = & \tupL(f(a))(g(b)) \\
 & = & (\tupL(f(a)) \circ g)(b)
\end{eqnarray*}$$
as claimed.
2. Let $a \in A$. Then
$$\begin{eqnarray*}
 &   & (\tPair(f,g) \circ \tupR(b))(a) \\
 & = & \tPair(f,g)(\tupR(b)(a)) \\
 & = & \tPair(f,g)(a,b) \\
 & = & (f(a),g(b)) \\
 & = & \tupR(g(b))(f(a)) \\
 & = & (\tupR(g(b)) \circ f)(a)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tpair_tupL :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> a -> b -> Bool)
> _test_tpair_tupL _ _ =
>   testName "tpair(f,g) . tupL(a) == tupL(f(a)) . g" $
>   \f g a b -> eq
>     (((tpair f g) . (tupL a)) b)
>     (((tupL (f a)) . g) b)
> 
> 
> _test_tpair_tupR :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> a -> b -> Bool)
> _test_tpair_tupR _ _ =
>   testName "tpair(f,g) . tupR(b) == tupR(g(b)) . f" $
>   \f g a b -> eq
>     (((tpair f g) . (tupR b)) a)
>     (((tupR (g b)) . f) a)

::::::::::::::::::::
::::::::::::::::::::

(@@@)

:::::: definition ::
Let $A$, $B$, and $C$ be sets. If $f : A \rightarrow B \rightarrow C$, we define $\uncurry(f) : A \times B \rightarrow C$ by $$\uncurry(f)(\tup(a)(b)) = f(a)(b).$$

In Haskell:

> uncurry :: (a -> b -> c) -> Pair a b -> c
> uncurry f (Pair a b) = f a b

::::::::::::::::::::


Testing
-------

Suite:

> _test_tuple
>   :: ( Show a, Show b, Show c
>      , Equal a, Equal b, Equal c
>      , Arbitrary a, Arbitrary b, Arbitrary c
>      , TypeName a, TypeName b, TypeName c
>      , CoArbitrary a, CoArbitrary b )
>   => a -> b -> c -> Int -> Int -> IO ()
> _test_tuple a b c size num = do
>   testLabel3 "Tuple" a b c
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_dup_fst_snd a b)
>   runTest args (_test_tswap_entries a b)
>   runTest args (_test_tswap_tswap a b)
>   runTest args (_test_tpair_apply a b)
>   runTest args (_test_tpair_tpair a b)
>   runTest args (_test_tassocL_entries a b c)
>   runTest args (_test_tassocR_entries a b c)
>   runTest args (_test_tassocL_tassocR a b c)
>   runTest args (_test_tassocR_tassocL a b c)
>   runTest args (_test_fst_tupL a b)
>   runTest args (_test_snd_tupL a b)
>   runTest args (_test_fst_tupR a b)
>   runTest args (_test_snd_tupR a b)
>   runTest args (_test_tswap_tupL a b)
>   runTest args (_test_tswap_tupR a b)
>   runTest args (_test_tpair_tupL a b)
>   runTest args (_test_tpair_tupR a b)

Main:

> main_tuple :: IO ()
> main_tuple = _test_tuple (true :: Bool) (true :: Bool) (true :: Bool) 20 100
