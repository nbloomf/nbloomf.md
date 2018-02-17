---
title: Disjoint Unions
author: nbloomf
date: 2017-12-21
tags: literate-haskell, arithmetic-made-difficult
slug: disjoint-unions
---

> {-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables #-}
> module DisjointUnions
>   ( Union(..), lft, rgt, either, uswap, upair , uassocL, uassocR, isLft, isRgt
>   , _test_disjoint_union, main_disjoint_union
>   ) where
> 
> import Testing
> import Functions
> import Booleans

Dual to sets of tuples are disjoint sums.

:::::: definition ::
[]{#def-disjoint-union}[]{#def-either-lft}[]{#def-either-rgt}
Let $A$ and $B$ be sets. There is a set $A + B$ together with two functions $\lft : A \rightarrow A + B$ and $\rgt : B \rightarrow A + B$ having the property that if $X$ is a set and $\sigma : A \rightarrow X$ and $\tau : B \rightarrow X$ functions then there is a unique map $\Theta : A + B \rightarrow X$ such that $\Theta \circ \lft = \sigma$ and $\Theta \circ \rgt = \tau$. That is, there is a unique $\Theta$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
A @>{\lft}>> A + B @<{\rgt}<< B \\
@V{\sigma}VV @VV{\Theta}V @VV{\tau}V \\
X @= X @= X
\end{CD}$$

We will denote this unique $\Theta : A + B \rightarrow X$ by $\either(\sigma,\tau)$.

More concretely, if $f : A + B \rightarrow X$ such that $f(\lft(a)) = \sigma(a)$ and $f(\rgt(b)) = \tau(b)$ for all $a \in A$ and $b \in B$, then $f = \either(\sigma,\tau)$.
::::::::::::::::::::

Now every element of $A+B$ is uniquely either of the form $\lft(a)$ or $\rgt(b)$ for some $a \in A$ or $b \in B$; this allows us to use case analysis on $A + B$. This set is sometimes called a *tagged union*, because it behaves like an ordinary set-theoretic union where elements are "tagged" with the set they came from (so, for instance, if $x \in A$ and $x \in B$, the $x$ from $A$ and the $x$ from $B$ are distinct in $A+B$).

:::::: theorem :::::
Let $A$ and $B$ be sets.

1. If $x \in A + B$, then either $x = \lft(a)$ for some $a \in A$ or $x = \rgt(b)$ for some $b \in B$.
2. There does not exist $x \in A + B$ such that $x = \lft(a)$ and $x = \rgt(b)$ for some $a \in A$ and $b \in B$.
3. $\lft : A \rightarrow A+B$ and $\rgt : B \rightarrow A+B$ are injective.

::: proof ::::::::::
1. Suppose to the contrary that there exists some $z \in A+B$ which is not of the form $\lft(a)$ or $\rgt(b)$ for any $a$ or $b$. Now consider $$f = \const(\btrue)$$ and $$g(x) = \\bif{\beq(x,z)}{\bfalse}{\btrue}$$ as functions $A+B \rightarrow \bool$. Note in particular that if $a \in A$ we have
$$\begin{eqnarray*}
 &   & \compose(f)(\lft)(a) \\
 &     \href{@functions@#def-compose}
   = & f(\lft(a)) \\
 &     \let{f = \const(\btrue)}
   = & \const(\btrue)(\lft(a)) \\
 &     \href{@functions@#def-const}
   = & \btrue \\
 &     \hyp{g(\lft(a)) = \btrue}
   = & g(\lft(a)) \\
 &     \href{@functions@#def-compose}
   = & \compose(g)(\lft)(a)
\end{eqnarray*}$$
since $z \neq \lft(a)$, and if $b \in B$ we have
$$\begin{eqnarray*}
 &   & \compose(f)(\rgt)(b) \\
 &     \href{@functions@#def-compose}
   = & f(\rgt(b)) \\
 &     \let{f = \const(\btrue)}
   = & \const(\btrue)(\rgt(b)) \\
 &     \href{@functions@#def-const}
   = & \btrue \\
 &     \hyp{g(\rgt(b)) = \btrue}
   = & g(\rgt(b)) \\
 &     \href{@functions@#def-compose}
   = & \compose(g)(\rgt)(b)
\end{eqnarray*}$$
similarly. By the universal property of $A + B$, we thus have $$f = \either(\const(\btrue),\const(\btrue)) = g.$$ But now we have $$\btrue = f(z) = g(z) = \bfalse,$$ which is absurd.
2. Suppose to the contrary that we have $z \in A + B$ with $\lft(a) = z = \rgt(b)$ for some $a \in A$ and $b \in B$, and consider now $f : A+B \rightarrow \bool$ given by $$f = \either(\const(\btrue),\const(\bfalse)).$$ We then have
$$\begin{eqnarray*}
 &   & \btrue \\
 &     \href{@functions@#def-const}
   = & \const(\btrue)(a) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \either(\const(\btrue),\const(\bfalse))(\lft(a)) \\
 &     \let{z = \lft(a)}
   = & \either(\const(\btrue),\const(\bfalse))(z) \\
 &     \let{z = \rgt(b)}
   = & \either(\const(\btrue),\const(\bfalse))(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \const(\bfalse)(b) \\
 &     \href{@functions@#def-const}
   = & \bfalse
\end{eqnarray*}$$
which is absurd.
3. Let $u,v \in A$, and suppose $\lft(u) = \lft(v)$. Now define $f : A \rightarrow \bool$ by
$$f(x) = \bif{\beq(x,u)}{\bfalse}{\btrue},$$ and consider $g = \either(f,\const(\btrue))$. We have
$$\begin{eqnarray*}
 &   & \bfalse \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\bfalse}{\btrue} \\
 &     \href{@testing@#thm-eq-reflexive}
   = & \bif{\beq(u,u)}{\bfalse}{\btrue} \\
 &     \let{f(x) = \bif{\beq(x,u)}{\bfalse}{\btrue}}
   = & f(u) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \either(f,\const(\btrue))(\lft(u)) \\
 &     \hyp{\lft(u) = \lft(v)}
   = & \either(f,\const(\btrue))(\lft(v)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & f(v) \\
 &     \let{f(x) = \bif{\beq(x,u)}{\bfalse}{\btrue}}
   = & \bif{\beq(v,u)}{\bfalse}{\btrue}
\end{eqnarray*}$$
thus $v = u$ as needed. A similar argument holds for $\rgt$.
::::::::::::::::::::
::::::::::::::::::::

The previous results suggest that we can model $A + B$ with the Haskell type ``Either a b``. For simplicity's sake we'll redefine this type, and the maps in the universal property, like so.

> data Union a b
>   = Left a | Right b
>   deriving Show
> 
> lft :: a -> Union a b
> lft a = Left a
> 
> rgt :: b -> Union a b
> rgt b = Right b
> 
> either :: (a -> x) -> (b -> x) -> Union a b -> x
> either f _ (Left  a) = f a
> either _ g (Right b) = g b
> 
> instance (Equal a, Equal b) => Equal (Union a b) where
>   eq (Left a1)  (Left a2)  = eq a1 a2
>   eq (Left _)   (Right _)  = false
>   eq (Right _)  (Left _)   = false
>   eq (Right b1) (Right b2) = eq b1 b2
> 
> instance (Arbitrary a, Arbitrary b) => Arbitrary (Union a b) where
>   arbitrary = do
>     s <- arbitrary
>     if s
>       then do
>         a <- arbitrary
>         return (Left a)
>       else do
>         b <- arbitrary
>         return (Right b)

For example, $\id_{A + B}$ is an $\either$.

:::::: theorem :::::
[]{#thm-either-lft-rgt}
Provided the types match up, we have $$\either(\lft,\rgt) = \id_{A + B}.$$

::: proof ::::::::::
If $a \in A$, we have
$$\begin{eqnarray*}
 &   & \compose(\id)(\lft)(a) \\
 &     \href{@functions@#def-compose}
   = & \id(\lft(a)) \\
 &     \href{@functions@#def-id}
   = & \lft(a)
\end{eqnarray*}$$
and likewise if $b \in B$ we have
$$\begin{eqnarray*}
 &   & \compose(\id)(\rgt)(b) \\
 &     \href{@functions@#def-compose}
   = & \id(\rgt(b)) \\
 &     \href{@functions@#def-id}
   = & \rgt(b)
\end{eqnarray*}$$
Since $\either(\lft,\rgt)$ is unique with this property, we have $\either(\lft,\rgt) = \id_{A+B}$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_either_lft_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (Union a b -> Bool)
> _test_either_lft_rgt _ _ =
>   testName "either(lft,rgt) == id" $
>   \x -> eq (either lft rgt x) x

::::::::::::::::::::
::::::::::::::::::::

We define $\uSwap$ on disjoint unions like so.

:::::: definition ::
[]{#def-uSwap}
Let $A$ and $B$ be sets. We define $\uSwap : A + B \rightarrow B + A$ by $$\uSwap = \either(\rgt,\lft).$$

In Haskell:

> uswap :: Union a b -> Union b a
> uswap = either rgt lft

::::::::::::::::::::

Now $\uSwap$ effectively toggles the tag of its argument.

:::::: theorem :::::
[]{#thm-uSwap-lft}[]{#thm-uSwap-rgt}[]{#thm-uSwap-involution}
Let $A$ and $B$ be sets. Then we have the following for all $a \in A$ and $b \in B$.

1. $\uSwap(\lft(a)) = \rgt(a)$.
2. $\uSwap(\rgt(b)) = \lft(b)$.
3. $\compose(\uSwap)(\uSwap) = \id$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \uSwap(\lft(a)) \\
 &     \href{@disjoint-unions@#def-uSwap}
   = & \either(\rgt,\lft)(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \rgt(a)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \uSwap(\rgt(a)) \\
 &     \href{@disjoint-unions@#def-uSwap}
   = & \either(\rgt,\lft)(\rgt(a)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \lft(a)
\end{eqnarray*}$$
as claimed.
3. Let $x \in A+B$; we have two possibilities. If $x = \lft(a)$, we have
$$\begin{eqnarray*}
 &   & \compose(\uSwap)(\uSwap)(\lft(a)) \\
 &     \href{@functions@#def-compose}
   = & \uSwap(\uSwap(\lft(a))) \\
 &     \href{@disjoint-unions@#thm-uSwap-lft}
   = & \uSwap(\rgt(a)) \\
 &     \href{@disjoint-unions@#thm-uSwap-rgt}
   = & \lft(a)
\end{eqnarray*}$$
and if $x = \rgt(b)$ we have
$$\begin{eqnarray*}
 &   & \compose(\uSwap)(\uSwap)(\rgt(b)) \\
 &     \href{@functions@#def-compose}
   = & \uSwap(\uSwap(\rgt(b))) \\
 &     \href{@disjoint-unions@#thm-uSwap-rgt}
   = & \uSwap(\lft(b)) \\
 &     \href{@disjoint-unions@#thm-uSwap-lft}
   = & \rgt(b)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_uswap_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_uswap_lft _ y =
>   testName "uswap(left(a)) == right(a)" $
>   \a -> eq
>     (uswap (lft a))
>     ((rgt a) `withTypeOf` (lft y))
> 
> 
> _test_uswap_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_uswap_rgt x _ =
>   testName "uswap(right(a)) == left(a)" $
>   \b -> eq
>     (uswap (rgt b))
>     ((lft b) `withTypeOf` (rgt x))
> 
> 
> _test_uswap_uswap :: (Equal a, Equal b)
>   => a -> b -> Test (Union a b -> Bool)
> _test_uswap_uswap _ _ =
>   testName "swap(swap(x)) == x" $
>   \x -> eq (uswap (uswap x)) x

::::::::::::::::::::
::::::::::::::::::::

Next, the utility $\uPair$ facilitates defining functions from one disjoint union to another.

:::::: definition ::
[]{#def-uPair}
Let $A$, $B$, $U$, and $V$ be sets. We define $\uPair : U^A \times V^B \rightarrow (U + V)^{A + B}$ by $$\uPair(f,g) = \either(\compose(\lft)(f),\compose(\rgt)(g)).$$

In Haskell:

> upair :: (a -> u) -> (b -> v) -> Union a b -> Union u v
> upair f g = either (lft . f) (rgt . g)

::::::::::::::::::::

$\uPair$ has some nice properties.

:::::: theorem :::::
[]{#thm-uPair-lft}[]{#thm-uPair-rgt}[]{#thm-uPair-compose}
For all $f$, $g$, $h$, $k$, $a$, and $b$ we have the following.

1. $\uPair(f,g)(\lft(a)) = \lft(f(a))$.
2. $\uPair(f,g)(\rgt(b)) = \rgt(g(b))$.
2. $\compose(\uPair(f,g))(\uPair(h,k)) = \uPair(\compose(f)(h),\compose(g)(k))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \uPair(f,g)(\lft(a)) \\
 &     \href{@disjoint-unions@#def-uPair}
   = & \either(\compose(\lft)(f),\compose(\rgt)(g))(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \compose(\lft)(f)(a) \\
 &     \href{@functions@#def-compose}
   = & \lft(f(a))
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \uPair(f,g)(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-uPair}
   = & \either(\compose(\lft)(f),\compose(\rgt)(g))(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \compose(\rgt)(g)(b) \\
 &     \href{@functions@#def-compose}
   = & \rgt(g(b))
\end{eqnarray*}$$
as claimed.
3. We consider two possibilities: note that
$$\begin{eqnarray*}
 &   & \compose(\uPair(f,g))(\uPair(h,k))(\lft(a)) \\
 &     \href{@functions@#def-compose}
   = & \uPair(f,g)(\uPair(h,k)(\lft(a))) \\
 &     \href{@disjoint-unions@#thm-uPair-lft}
   = & \uPair(f,g)(\lft(h(a))) \\
 &     \href{@disjoint-unions@#thm-uPair-lft}
   = & \lft(f(h(a))) \\
 &     \href{@functions@#def-compose}
   = & \lft(\compose(f)(h)(a)) \\
 &     \href{@disjoint-unions@#thm-uPair-lft}
   = & \uPair(\compose(f)(h),\compose(g)(k))(\lft(a))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \compose(\uPair(f,g))(\uPair(h,k))(\rgt(b)) \\
 &     \href{@functions@#def-compose}
   = & \uPair(f,g)(\uPair(h,k)(\rgt(b))) \\
 &     \href{@disjoint-unions@#thm-uPair-rgt}
   = & \uPair(f,g)(\rgt(k(b))) \\
 &     \href{@disjoint-unions@#thm-uPair-rgt}
   = & \rgt(g(k(b))) \\
 &     \href{@functions@#def-compose}
   = & \rgt(\compose(g)(k)(b)) \\
 &     \href{@disjoint-unions@#thm-uPair-rgt}
   = & \uPair(\compose(f)(h),\compose(g)(k))(\rgt(b))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_upair_lft :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> a -> Bool)
> _test_upair_lft _ y =
>   testName "upair(f,g)(lft(a)) == lft(f(a))" $
>   \f g a -> eq
>     (upair f g ((lft a) `withTypeOf` (rgt y)))
>     ((lft (f a)) `withTypeOf` (rgt y))
> 
> 
> _test_upair_rgt :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> b -> Bool)
> _test_upair_rgt x _ =
>   testName "upair(f,g)(rgt(b)) == rgt(g(b))" $
>   \f g b -> eq
>     (upair f g ((rgt b) `withTypeOf` (lft x)))
>     ((rgt (g b)) `withTypeOf` (lft x))
> 
> 
> _test_upair_upair :: (Equal a, Equal b)
>   => a -> b
>   -> Test ((a -> a) -> (b -> b) -> (a -> a) -> (b -> b)
>       -> Union a b -> Bool)
> _test_upair_upair _ _ =
>   testName "upair(f,g) . upair(h,k) == upair(f . h, g . k)" $
>   \f g h k x ->
>     eq
>       (upair f g (upair h k x))
>       (upair (f . h) (g . k) x)

::::::::::::::::::::
::::::::::::::::::::

Finally, note that although as sets $A + (B + C)$ and $(A + B) + C$ cannot possibly be equal to each other in general, they are naturally isomorphic via $\uAssocL$ and $\uAssocR$.

:::::: definition ::
[]{#def-uAssocL}[]{#def-uAssocR}
Let $A$, $B$, and $C$ be sets. We define $\uAssocL : A + (B + C) \rightarrow (A + B) + C$ by $$\uAssocL = \either(\compose(\lft)(\lft),\either(\compose(\lft)(\rgt),\rgt))$$ and define $\uAssocR : (A + B) + C \rightarrow A + (B + C)$ by $$\uAssocR = \either(\either(\lft,\compose(\rgt)(\lft)),\compose(\rgt)(\rgt)).$$

In Haskell:

> uassocL :: Union a (Union b c) -> Union (Union a b) c
> uassocL = either (lft . lft) (either (lft . rgt) rgt)
> 
> uassocR :: Union (Union a b) c -> Union a (Union b c)
> uassocR = either (either lft (rgt . lft)) (rgt . rgt)

::::::::::::::::::::

Now $\uAssocL$ and $\uAssocR$ have some nice properties.

:::::: theorem :::::
[]{#thm-uAssocL-lft}[]{#thm-uAssocL-rgt-lft}[]{#thm-uAssocL-rgt-rgt}[]{#thm-uAssocR-lft-lft}[]{#thm-uAssocR-lft-rgt}[]{#thm-uAssocR-rgt}[]{#thm-uAssocR-uAssocL}[]{#thm-uAssocL-uAssocR}
The following hold whenever everything has the appropriate type.

1. $\uAssocL(\lft(a)) = \lft(\lft(a))$.
2. $\uAssocL(\rgt(\lft(b))) = \lft(\rgt(b))$.
3. $\uAssocL(\rgt(\rgt(c))) = \rgt(c)$.
4. $\uAssocR(\lft(\lft(a))) = \lft(a)$.
5. $\uAssocR(\lft(\rgt(b))) = \rgt(\lft(b))$.
6. $\uAssocR(\rgt(c)) = \rgt(\rgt(c))$.
7. $\compose(\uAssocR)(\uAssocL) = \id_{A + (B + C)}$.
8. $\compose(\uAssocL)(\uAssocR) = \id_{(A + B) + C}$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\lft(a)) \\
 &     \href{@disjoint-unions@#def-uAssocL}
   = & \either(\compose(\lft)(\lft),\either(\compose(\lft)(\rgt),\rgt))(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \compose(\lft)(\lft)(a) \\
 &     \href{@functions@#def-compose}
   = & \lft(\lft(a))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\rgt(\lft(b))) \\
 &     \href{@disjoint-unions@#def-uAssocL}
   = & \either(\compose(\lft)(\lft),\either(\compose(\lft)(\rgt),\rgt))(\rgt(\lft(b))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \either(\compose(\lft)(\rgt),\rgt)(\lft(b)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \compose(\lft)(\rgt)(b) \\
 &     \href{@functions@#def-compose}
   = & \lft(\rgt(b))
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\rgt(\rgt(c))) \\
 &     \href{@disjoint-unions@#def-uAssocL}
   = & \either(\compose(\lft)(\lft),\either(\compose(\lft)(\rgt),\rgt))(\rgt(\rgt(c))) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \either(\compose(\lft)(\rgt),\rgt)(\rgt(c)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \rgt(c)
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\lft(\lft(a))) \\
 &     \href{@disjoint-unions@#def-uAssocR}
   = & \either(\either(\lft,\compose(\rgt)(\lft)),\compose(\rgt)(\rgt))(\lft(\lft(a))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \either(\lft,\compose(\rgt)(\lft))(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \lft(a)
\end{eqnarray*}$$
as claimed.
5. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\lft(\rgt(b))) \\
 &     \href{@disjoint-unions@#def-uAssocR}
   = & \either(\either(\lft,\compose(\rgt)(\lft)),\compose(\rgt)(\rgt))(\lft(\rgt(b))) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \either(\lft,\compose(\rgt)(\lft))(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \compose(\rgt)(\lft)(b) \\
 &     \href{@functions@#def-compose}
   = & \rgt(\lft(b))
\end{eqnarray*}$$
as claimed.
6. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\rgt(c)) \\
 &     \href{@disjoint-unions@#def-uAssocR}
   = & \either(\either(\lft,\compose(\rgt)(\lft)),\compose(\rgt)(\rgt))(\rgt(c)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \compose(\rgt)(\rgt)(c) \\
 &     \href{@functions@#def-compose}
   = & \rgt(\rgt(c))
\end{eqnarray*}$$
as claimed.
7. If $x \in A + (B + C)$, we have three possibilities. If $x = \lft(a)$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocR)(\uAssocL)(x) \\
 &     \let{x = \lft(a)}
   = & \compose(\uAssocR)(\uAssocL)(\lft(a)) \\
 &     \href{@functions@#def-compose}
   = & \uAssocR(\uAssocL(\lft(a))) \\
 &     \href{@disjoint-unions@#thm-uAssocL-lft}
   = & \uAssocR(\lft(\lft(a))) \\
 &     \href{@disjoint-unions@#thm-uAssocR-lft-lft}
   = & \lft(a) \\
 &     \let{x = \lft(a)}
   = & x
\end{eqnarray*}$$
if $x = \rgt(\lft(b))$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocR)(\uAssocL)(x) \\
 &     \let{x = \rgt(\lft(b))}
   = & \compose(\uAssocR)(\uAssocL)(\rgt(\lft(b))) \\
 &     \href{@functions@#def-compose}
   = & \uAssocR(\uAssocL(\rgt(\lft(b)))) \\
 &     \href{@disjoint-unions@#thm-uAssocL-rgt-lft}
   = & \uAssocR(\lft(\rgt(b))) \\
 &     \href{@disjoint-unions@#thm-uAssocR-lft-rgt}
   = & \rgt(\lft(b)) \\
 &     \let{x = \rgt(\lft(b))}
   = & x
\end{eqnarray*}$$
and if $x = \rgt(\rgt(c))$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocR)(\uAssocL)(x) \\
 &     \let{x = \rgt(\rgt(c))}
   = & \compose(\uAssocR)(\uAssocL)(\rgt(\rgt(c))) \\
 &     \href{@functions@#def-compose}
   = & \uAssocR(\uAssocL(\rgt(\rgt(c)))) \\
 &     \href{@disjoint-unions@#thm-uAssocL-rgt-rgt}
   = & \uAssocR(\rgt(c)) \\
 &     \href{@disjoint-unions@#thm-uAssocR-rgt}
   = & \rgt(\rgt(c)) \\
 &     \let{x = \rgt(\rgt(c))}
   = & x
\end{eqnarray*}$$
as needed.
8. If $x \in (A + B) + C$, we have three possibilities. If $x = \lft(\lft(a))$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocL)(\uAssocR)(x) \\
 &     \let{x = \lft(\lft(a))}
   = & \compose(\uAssocL)(\uAssocR)(\lft(\lft(a))) \\
 &     \href{@functions@#def-compose}
   = & \uAssocL(\uAssocR(\lft(\lft(a)))) \\
 &     \href{@disjoint-unions@#thm-uAssocR-lft-lft}
   = & \uAssocL(\lft(a)) \\
 &     \href{@disjoint-unions@#thm-uAssocL-lft}
   = & \lft(\lft(a)) \\
 &     \let{x = \lft(\lft(a))}
   = & x
\end{eqnarray*}$$
if $x = \lft(\rgt(b))$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocL)(\uAssocR)(x) \\
 &     \let{x = \lft(\rgt(b))}
   = & \compose(\uAssocL)(\uAssocR)(\lft(\rgt(b))) \\
 &     \href{@functions@#def-compose}
   = & \uAssocL(\uAssocR(\lft(\rgt(b)))) \\
 &     \href{@disjoint-unions@#thm-uAssocR-lft-rgt}
   = & \uAssocL(\rgt(\lft(b))) \\
 &     \href{@disjoint-unions@#thm-uAssocL-rgt-lft}
   = & \lft(\rgt(b)) \\
 &     \let{x = \lft(\rgt(b))}
   = & x
\end{eqnarray*}$$
and if $x = \rgt(c)$, note that
$$\begin{eqnarray*}
 &   & \compose(\uAssocL)(\uAssocR)(x) \\
 &     \let{x = \rgt(c)}
   = & \compose(\uAssocL)(\uAssocR)(\rgt(c)) \\
 &     \href{@functions@#def-compose}
   = & \uAssocL(\uAssocR(\rgt(c))) \\
 &     \href{@disjoint-unions@#thm-uAssocR-rgt}
   = & \uAssocL(\rgt(\rgt(c))) \\
 &     \href{@disjoint-unions@#thm-uAssocL-rgt-rgt}
   = & \rgt(c) \\
 &     \let{x = \rgt(c)}
   = & x
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_uassocL_lft :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> Bool)
> _test_uassocL_lft _ y z =
>   testName "uassocL(lft(a)) == lft(lft(a))" $
>   \a ->
>     let w = (lft y) `withTypeOf` (rgt z)
>     in eq
>       (uassocL ((lft a) `withTypeOf` (rgt w)))
>       (lft (lft a))
> 
> 
> _test_uassocL_rgt_lft :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (b -> Bool)
> _test_uassocL_rgt_lft x _ z =
>   testName "uassocL(rgt(lft(b))) == lft(rgt(b))" $
>   \b -> eq
>     (uassocL 
>       ((rgt ((lft b) `withTypeOf` (rgt z)) `withTypeOf` (lft x))))
>     (lft (rgt b))
> 
> 
> _test_uassocL_rgt_rgt :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (c -> Bool)
> _test_uassocL_rgt_rgt x y _ =
>   testName "uassocL(rgt(rgt(c))) == rgt(c)" $
>   \c -> eq
>     (uassocL
>       ((rgt ((rgt c) `withTypeOf` (lft y)) `withTypeOf` (lft x))))
>     (rgt c)
> 
> 
> _test_uassocR_lft_lft :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> Bool)
> _test_uassocR_lft_lft _ y z =
>   testName "uassocR(lft(lft(a))) == lft(a)" $
>   \a -> eq
>     (uassocR
>       ((lft ((lft a) `withTypeOf` (rgt y)) `withTypeOf` (rgt z))))
>     (lft a)
> 
> 
> _test_uassocR_lft_rgt :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (b -> Bool)
> _test_uassocR_lft_rgt x _ z =
>   testName "uassocR(lft(rgt(b))) == rgt(lft(b))" $
>   \b -> eq
>     (uassocR
>       ((lft ((rgt b) `withTypeOf` (lft x)) `withTypeOf` (rgt z))))
>     (rgt (lft b))
> 
> 
> _test_uassocR_rgt :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (c -> Bool)
> _test_uassocR_rgt x y _ =
>   testName "uassocR(rgt(c)) == rgt(rgt(c))" $
>   \c ->
>     let w = (lft x) `withTypeOf` (rgt y)
>     in eq
>       (uassocR ((rgt c) `withTypeOf` (lft w)))
>       (rgt (rgt c))
> 
> 
> _test_uassocR_uassocL :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (Union a (Union b c) -> Bool)
> _test_uassocR_uassocL _ _ _ =
>   testName "uassocR . uassocL == id" $
>   \x -> eq (uassocR (uassocL x)) x
> 
> 
> _test_uassocL_uassocR :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (Union (Union a b) c -> Bool)
> _test_uassocL_uassocR _ _ _ =
>   testName "uassocL . uassocR == id" $
>   \x -> eq (uassocL (uassocR x)) x

::::::::::::::::::::
::::::::::::::::::::

We also define some helper functions which detect whether an element of $A + B$ is a $\lft$ or a $\rgt$.

:::::: definition ::
[]{#dfn-isRgt}[]{#dfn-isLft}
Let $A$ and $B$ be sets. We define $\isLft : A + B \rightarrow \bool$ by $$\isLft = \either(\const(\btrue),\const(\bfalse))$$ and $\isRgt : A + B \rightarrow \bool$ by $$\isRgt = \either(\const(\bfalse),\const(\btrue)).$$

In Haskell:

> isLft :: Union a b -> Bool
> isLft = either (const true) (const false)
> 
> isRgt :: Union a b -> Bool
> isRgt = either (const false) (const true)

::::::::::::::::::::

Now $\isLft$ and $\isRgt$ have some nice properties.

:::::: theorem :::::
[]{#thm-isLft-lft}[]{#thm-isLft-rgt}[]{#thm-isRgt-lft}[]{#thm-isRgt-rgt}
Let $A$ and $B$ be sets. Then we have the following for all $a \in A$ and $b \in B$.

1. $\isLft(\lft(a)) = \btrue$.
2. $\isLft(\rgt(b)) = \bfalse$.
3. $\isRgt(\lft(a)) = \bfalse$.
4. $\isRgt(\rgt(b)) = \btrue$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \isLft(\lft(a)) \\
 &     \href{@disjoint-unions@#dfn-isLft}
   = & \either(\const(\btrue),\const(\bfalse))(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\btrue)(a) \\
 &     \href{@functions@#def-const}
   = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \isLft(\rgt(b)) \\
 &     \href{@disjoint-unions@#dfn-isLft}
   = & \either(\const(\btrue),\const(\bfalse))(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \const(\bfalse)(b) \\
 &     \href{@functions@#def-const}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \isRgt(\lft(a)) \\
 &     \href{@disjoint-unions@#dfn-isRgt}
   = & \either(\const(\bfalse),\const(\btrue))(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \const(\bfalse)(a) \\
 &     \href{@functions@#def-const}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \isRgt(\rgt(b)) \\
 &     \href{@disjoint-unions@#dfn-isRgt}
   = & \either(\const(\bfalse),\const(\btrue))(\rgt(b)) \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \const(\btrue)(b) \\
 &     \href{@functions@#def-const}
   = & \btrue
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_isLft_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_isLft_lft _ y =
>   testName "isLft(lft(a)) == true" $
>   \a -> eq (isLft ((lft a) `withTypeOf` (rgt y))) true
> 
> 
> _test_isLft_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_isLft_rgt x _ =
>   testName "isLft(rgt(b)) == false" $
>   \b -> eq (isLft ((rgt b) `withTypeOf` (lft x))) false
> 
> 
> _test_isRgt_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_isRgt_lft _ y =
>   testName "isRgt(lft(a)) == false" $
>   \a -> eq (isRgt ((lft a) `withTypeOf` (rgt y))) false
> 
> 
> _test_isRgt_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_isRgt_rgt x _ =
>   testName "isRgt(rgt(b)) == true" $
>   \b -> eq (isRgt ((rgt b) `withTypeOf` (lft x))) true

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_disjoint_union
>   :: ( Show a, Show b, Show c
>      , Equal a, Equal b, Equal c
>      , Arbitrary a, Arbitrary b, Arbitrary c
>      , TypeName a, TypeName b, TypeName c
>      , CoArbitrary a, CoArbitrary b )
>   => a -> b -> c -> Int -> Int -> IO ()
> _test_disjoint_union a b c size num = do
>   testLabel3 "Disjoint Union" a b c
> 
>   let
~ args = testArgs size cases
> 
>   runTest args (_test_either_lft_rgt a b)
> 
>   runTest args (_test_uswap_lft a b)
>   runTest args (_test_uswap_rgt a b)
>   runTest args (_test_uswap_uswap a b)
> 
>   runTest args (_test_upair_lft a b)
>   runTest args (_test_upair_rgt a b)
>   runTest args (_test_upair_upair a b)
> 
>   runTest args (_test_uassocL_lft a b c)
>   runTest args (_test_uassocL_rgt_lft a b c)
>   runTest args (_test_uassocL_rgt_rgt a b c)
>   runTest args (_test_uassocR_lft_lft a b c)
>   runTest args (_test_uassocR_lft_rgt a b c)
>   runTest args (_test_uassocR_rgt a b c)
>   runTest args (_test_uassocR_uassocL a b c)
>   runTest args (_test_uassocL_uassocR a b c)
> 
>   runTest args (_test_isLft_lft a b)
>   runTest args (_test_isLft_rgt a b)
>   runTest args (_test_isRgt_lft a b)
>   runTest args (_test_isRgt_rgt a b)


Main:

> main_disjoint_union :: IO ()
> main_disjoint_union = do
>   _test_disjoint_union (true :: Bool) (true :: Bool) (true :: Bool) 20 100
