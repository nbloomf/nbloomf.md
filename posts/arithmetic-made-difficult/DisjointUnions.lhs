---
title: Disjoint Unions
author: nbloomf
date: 2017-12-21
tags: literate-haskell, arithmetic-made-difficult
slug: disjoint-unions
---

> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE NoImplicitPrelude #-}
> module DisjointUnions
>   ( lft, rgt, either, uswap, upair , uassocL, uassocR, isLft, isRgt
>   , _test_disjoint_union, main_disjoint_union
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies

Dual to sets of tuples are disjoint sums.

<div class="result">
<div class="defn"><a name="dfn-disjoint-union" />
Let $A$ and $B$ be sets. There is a set $A + B$ together with two functions $\lft : A \rightarrow A + B$ and $\rgt : B \rightarrow A + B$ having the property that if $X$ is a set and $\sigma : A \rightarrow X$ and $\tau : B \rightarrow X$ functions then there is a unique map $\Theta : A + B \rightarrow X$ such that $\Theta \circ \lft = \sigma$ and $\Theta \circ \rgt = \tau$. That is, there is a unique $\Theta$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
A @>{\lft}>> A + B @<{\rgt}<< B \\
@V{\sigma}VV @VV{\Theta}V @VV{\tau}V \\
X @= X @= X
\end{CD}$$

We will denote this unique $\Theta : A + B \rightarrow X$ by $\either(\sigma,\tau)$.

More concretely, if $f : A + B \rightarrow X$ such that $f(\lft(a)) = \sigma(a)$ and $f(\rgt(b)) = \tau(b)$ for all $a \in A$ and $b \in B$, then $f = \either(\sigma,\tau)$.
</div>
</div>

Now every element of $A+B$ is uniquely either of the form $\lft(a)$ or $\rgt(b)$ for some $a \in A$ or $b \in B$; this allows us to use case analysis on $A + B$. This set is sometimes called a *tagged union*, because it behaves like an ordinary set-theoretic union where elements are "tagged" with the set they came from (so, for instance, if $x \in A$ and $x \in B$, the $x$ from $A$ and the $x$ from $B$ are distinct in $A+B$).

<div class="result">
<div class="thm">
Let $A$ and $B$ be sets.

1. If $x \in A + B$, then either $x = \lft(a)$ for some $a \in A$ or $x = \rgt(b)$ for some $b \in B$.
2. There does not exist $x \in A + B$ such that $x = \lft(a)$ and $x = \rgt(b)$ for some $a \in A$ and $b \in B$.
3. $\lft : A \rightarrow A+B$ and $\rgt : B \rightarrow A+B$ are injective.
</div>

<div class="proof"><p>
1. Suppose to the contrary that there exists some $z \in A+B$ which is not of the form $\lft(a)$ or $\rgt(b)$ for any $a$ or $b$. Now consider the following two functions $A+B \rightarrow \bool$: $$\Psi(x) = \btrue$$ and
$$\Omega(x) = \left\{\begin{array}{ll}
 \bfalse & \mathrm{if}\ x = z \\
 \btrue  & \mathrm{otherwise.}
\end{array}\right.$$
Note in particular that if $a \in A$ we have
$$\begin{eqnarray*}
 &   & (\Omega \circ \lft)(a) \\
 & = & \Omega(\lft(a)) \\
 & = & \btrue \\
 & = & \Psi(\lft(a)) \\
 & = & (\Psi \circ \lft)(a)
\end{eqnarray*}$$
since $z \neq \lft(a)$, and if $b \in B$ we have
$$\begin{eqnarray*}
 &   & (\Omega \circ \rgt)(b) \\
 & = & \Omega(\rgt(b)) \\
 & = & \btrue \\
 & = & \Psi(\rgt(b)) \\
 & = & (\Psi \circ \rgt)(b)
\end{eqnarray*}$$
similarly. By the universal property of $A + B$, we thus have $$\Psi = \either(\const(\btrue),\const(\btrue)) = \Omega.$$ But now we have $$\btrue = \Psi(z) = \Omega(z) = \bfalse,$$ which is absurd.
2. Suppose to the contrary that we have $z \in A + B$ with $\lft(a) = z = \rgt(b)$ for some $a \in A$ and $b \in B$, and consider now $\Theta : A+B \rightarrow \bool$ given by $$\Theta = \either(\const(\btrue),\const(\bfalse)).$$ We then have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \const(\btrue)(a) \\
 & = & (\Theta \circ \lft)(a) \\
 & = & \Theta(\lft(a)) \\
 & = & \Theta(z) \\
 & = & \Theta(\rgt(b)) \\
 & = & (\Theta \circ \rgt)(b) \\
 & = & \const(\bfalse)(b) \\
 & = & \bfalse,
\end{eqnarray*}$$
which is absurd.
3. Let $u,v \in A$, and suppose $\lft(u) = \lft(v)$. Now define $f : A \rightarrow \bool$ by
$$f(x) = \left\{\begin{array}{ll}
 \bfalse & \mathrm{if}\ x = u \\
 \btrue  & \mathrm{otherwise},
\end{array}\right.$$
and consider $\Theta = \either(f,\const(\btrue))$. We have
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & f(u) \\
 & = & (\Theta \circ \lft)(u) \\
 & = & \Theta(\lft(u)) \\
 & = & \Theta(\lft(v)) \\
 & = & (\Theta \circ \lft)(v) \\
 & = & f(v);
\end{eqnarray*}$$
thus $v = u$ as needed. A similar argument holds for $\rgt$.
</p></div>
</div>

The previous results suggest that we can model $A + B$ with the Haskell type ``Either a b``, and the maps in the universal property like so.

> lft :: a -> Either a b
> lft a = Left a
> 
> rgt :: b -> Either a b
> rgt b = Right b
> 
> either :: (a -> x) -> (b -> x) -> Either a b -> x
> either f _ (Left  a) = f a
> either _ g (Right b) = g b

For example, $\id_{A + B}$ is an $\either$.

<div class="result">
<div class="thm"><p>
Provided the types match up, we have $$\either(\lft,\rgt) = \id_{A + B}.$$
</p></div>

<div class="proof"><p>
If $a \in A$, we have
$$\begin{eqnarray*}
 &   & (\id_{A + B} \circ \lft)(a) \\
 & = & \id_{A+B}(\lft(a)) \\
 & = & \lft(a)
\end{eqnarray*}$$
and likewise if $b \in B$ we have
$$\begin{eqnarray*}
 &   & (\id_{A + B} \circ \rgt)(a) \\
 & = & \id_{A + B}(\rgt(b)) \\
 & = & \rgt(b).
\end{eqnarray*}$$
Since $\either(\lft,\rgt)$ is unique with this property, we have $\either(\lft,\rgt) = \id_{A+B}$ as claimed.
</p></div>

<div class="test"><p>

> _test_either_lft_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (Either a b -> Bool)
> _test_either_lft_rgt _ _ =
>   testName "either(lft,rgt) == id" $
>   \x -> eq (either lft rgt x) x

</p></div>
</div>

We define $\uSwap$ on disjoint unions like so.

<div class="result">
<div class="defn"><a name="dfn-uswap" />
Let $A$ and $B$ be sets. We define $\uSwap : A + B \rightarrow B + A$ by $$\uSwap = \either(\rgt,\lft).$$

In Haskell:

> uswap :: Either a b -> Either b a
> uswap = either rgt lft

</div>
</div>

Now $\uSwap$ effectively toggles the tag of its argument.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then we have the following for all $a \in A$ and $b \in B$.

1. $\uSwap(\lft(a)) = \rgt(a)$.
2. $\uSwap(\rgt(b)) = \lft(b)$.
3. $\uSwap \circ \uSwap = \id_{A + B}$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \uSwap(\lft(a)) \\
 & = & \either(\rgt,\lft)(\lft(a)) \\
 & = & \rgt(a)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \uSwap(\rgt(a)) \\
 & = & \either(\rgt,\lft)(\lft(a)) \\
 & = & \rgt(a)
\end{eqnarray*}$$
as claimed.
3. Let $x \in A+B$; we have two possibilities. If $x = \lft(a)$, we have
$$\begin{eqnarray*}
 &   & (\uSwap \circ \uSwap)(\lft(a)) \\
 & = & \uSwap(\uSwap(\lft(a))) \\
 & = & \uSwap(\rgt(a)) \\
 & = & \lft(a),
\end{eqnarray*}$$
and if $x = \rgt(b)$ we have
$$\begin{eqnarray*}
 &   & (\uSwap \circ \uSwap)(\rgt(b)) \\
 & = & \uSwap(\uSwap(\rgt(b))) \\
 & = & \uSwap(\lft(b)) \\
 & = & \rgt(b)
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

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
>   => a -> b -> Test (Either a b -> Bool)
> _test_uswap_uswap _ _ =
>   testName "swap(swap(x)) == x" $
>   \x -> eq (uswap (uswap x)) x

</p></div>
</div>

Next, the utility $\uPair$ facilitates defining functions from one disjoint union to another.

<div class="result">
<div class="defn"><p>
Let $A$, $B$, $U$, and $V$ be sets. We define $\uPair : U^A \times V^B \rightarrow (U + V)^{A + B}$ by $$\uPair(f,g) = \either(\lft \circ f, \rgt \circ g).$$

In Haskell:

> upair :: (a -> u) -> (b -> v) -> Either a b -> Either u v
> upair f g = either (lft . f) (rgt . g)

</p></div>
</div>

$\uPair$ has some nice properties.

<div class="result">
<div class="thm">
For all $f$, $g$, $h$, $k$, $a$, and $b$ we have the following.

1. $\uPair(f,g)(\lft(a)) = \lft(f(a))$.
2. $\uPair(f,g)(\rgt(b)) = \rgt(g(b))$.
2. $\uPair(f,g) \circ \uPair(h,k) = \uPair(f \circ h, g \circ k)$.
</div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \uPair(f,g)(\lft(a)) \\
 & = & \either(\lft \circ f, \rgt \circ g)(\lft(a)) \\
 & = & (\lft \circ f)(a) \\
 & = & \lft(f(a))
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \uPair(f,g)(\rgt(b)) \\
 & = & \either(\lft \circ f, \rgt \circ g)(\rgt(b)) \\
 & = & (\rgt \circ g)(b) \\
 & = & \rgt(g(b))
\end{eqnarray*}$$
as claimed.
3. We consider two possibilities: note that
$$\begin{eqnarray*}
 &   & (\uPair(f,g) \circ \uPair(h,k))(\lft(a)) \\
 & = & \uPair(f,g)(\uPair(h,k)(\lft(a))) \\
 & = & \uPair(f,g)(\lft(h(a))) \\
 & = & \lft(f(h(a))) \\
 & = & \uPair(f \circ h, g \circ k)(\lft(a))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & (\uPair(f,g) \circ \uPair(h,k))(\rgt(b)) \\
 & = & \uPair(f,g)(\uPair(h,k)(\rgt(b))) \\
 & = & \uPair(f,g)(\rgt(h(b))) \\
 & = & \rgt(g(k(b))) \\
 & = & \uPair(f \circ h, g \circ k)(\rgt(b))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

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
>       -> Either a b -> Bool)
> _test_upair_upair _ _ =
>   testName "upair(f,g) . upair(h,k) == upair(f . h, g . k)" $
>   \f g h k x ->
>     eq
>       (upair f g (upair h k x))
>       (upair (f . h) (g . k) x)

</p></div>
</div>

Finally, note that although as sets $A + (B + C)$ and $(A + B) + C$ cannot possibly be equal to each other in general, they are naturally isomorphic via $\uAssocL$ and $\uAssocR$.

<div class="result">
<div class="defn">
Let $A$, $B$, and $C$ be sets. We define $\uAssocL : A + (B + C) \rightarrow (A + B) + C$ by $$\uAssocL = \either(\lft \circ \lft, \either(\lft \circ \rgt, \rgt))$$ and define $\uAssocR : (A + B) + C \rightarrow A + (B + C)$ by $$\uAssocR = \either(\either(\lft,\rgt \circ \lft),\rgt \circ \rgt).$$

In Haskell:

> uassocL :: Either a (Either b c) -> Either (Either a b) c
> uassocL = either (lft . lft) (either (lft . rgt) rgt)
> 
> uassocR :: Either (Either a b) c -> Either a (Either b c)
> uassocR = either (either lft (rgt . lft)) (rgt . rgt)

</div>
</div>

Now $\uAssocL$ and $\uAssocR$ have some nice properties.

<div class="result">
<div class="thm"><p>
The following hold whenever everything has the appropriate type.

1. $\uAssocL(\lft(a)) = \lft(\lft(a))$.
2. $\uAssocL(\rgt(\lft(b))) = \lft(\rgt(b))$.
3. $\uAssocL(\rgt(\rgt(c))) = \rgt(c)$.
4. $\uAssocR(\lft(\lft(a))) = \lft(a)$.
5. $\uAssocR(\lft(\rgt(b))) = \rgt(\lft(b))$.
6. $\uAssocR(\rgt(c)) = \rgt(\rgt(c))$.
7. $\uAssocR \circ \uAssocL = \id_{A + (B + C)}$.
8. $\uAssocL \circ \uAssocR = \id_{(A + B) + C}$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\lft(a)) \\
 & = & \either(\lft \circ \lft, \either(\lft \circ \rgt, \rgt))(\lft(a)) \\
 & = & (\lft \circ \lft)(a) \\
 & = & \lft(\lft(a))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\rgt(\lft(b))) \\
 & = & \either(\lft \circ \lft, \either(\lft \circ \rgt, \rgt))(\rgt(\lft(b))) \\
 & = & \either(\lft \circ \rgt, \rgt)(\lft(b)) \\
 & = & (\lft \circ \rgt)(b) \\
 & = & \lft(\rgt(b))
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \uAssocL(\rgt(\rgt(c))) \\
 & = & \either(\lft \circ \lft, \either(\lft \circ \rgt, \rgt))(\rgt(\rgt(c))) \\
 & = & \either(\lft \circ \rgt, \rgt)(\rgt(c)) \\
 & = & \rgt(c)
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\lft(\lft(a))) \\
 & = & \either(\either(\lft,\rgt \circ \lft),\rgt \circ \rgt)(\lft(\lft(a))) \\
 & = & \either(\lft,\rgt \circ \lft)(\lft(a)) \\
 & = & \lft(a)
\end{eqnarray*}$$
as claimed.
5. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\lft(\rgt(b))) \\
 & = & \either(\either(\lft,\rgt \circ \lft),\rgt \circ \rgt)(\lft(\rgt(b))) \\
 & = & \either(\lft,\rgt \circ \lft)(\rgt(b)) \\
 & = & (\rgt \circ \lft)(b) \\
 & = & \rgt(\lft(b))
\end{eqnarray*}$$
as claimed.
6. We have
$$\begin{eqnarray*}
 &   & \uAssocR(\rgt(c)) \\
 & = & \either(\either(\lft,\rgt \circ \lft),\rgt \circ \rgt)(\rgt(c)) \\
 & = & (\rgt \circ \rgt)(c) \\
 & = & \rgt(\rgt(c))
\end{eqnarray*}$$
as claimed.
7. If $x \in A + (B + C)$, we have three possibilities. If $x = \lft(a)$, note that
$$\begin{eqnarray*}
 &   & (\uAssocR \circ \uAssocL)(x) \\
 & = & \uAssocR(\uAssocL(\lft(a))) \\
 & = & \uAssocR(\lft(\lft(a))) \\
 & = & \lft(a) \\
 & = & x;
\end{eqnarray*}$$
if $x = \rgt(\lft(b))$, note that
$$\begin{eqnarray*}
 &   & (\uAssocR \circ \uAssocL)(x) \\
 & = & \uAssocR(\uAssocL(\rgt(\lft(b)))) \\
 & = & \uAssocR(\lft(\rgt(b))) \\
 & = & \rgt(\lft(b)) \\
 & = & x;
\end{eqnarray*}$$
and if $x = \rgt(\rgt(c))$, note that
$$\begin{eqnarray*}
 &   & (\uAssocR \circ \uAssocL)(x) \\
 & = & \uAssocR(\uAssocL(\rgt(\rgt(c)))) \\
 & = & \uAssocR(\rgt(c)) \\
 & = & \rgt(\rgt(c)) \\
 & = & x,
\end{eqnarray*}$$
as needed.
8. If $x \in (A + B) + C$, we have three possibilities. If $x = \lft(\lft(a))$, note that
$$\begin{eqnarray*}
 &   & (\uAssocL \circ \uAssocR)(x) \\
 & = & \uAssocL(\uAssocR(\lft(\lft(a)))) \\
 & = & \uAssocL(\lft(a)) \\
 & = & \lft(\lft(a)) \\
 & = & x;
\end{eqnarray*}$$
if $x = \lft(\rgt(b))$, note that
$$\begin{eqnarray*}
 &   & (\uAssocL \circ \uAssocR)(x) \\
 & = & \uAssocL(\uAssocR(\lft(\rgt(b)))) \\
 & = & \uAssocL(\rgt(\lft(b))) \\
 & = & \lft(\rgt(b)) \\
 & = & x;
\end{eqnarray*}$$
and if $x = \rgt(c)$, note that
$$\begin{eqnarray*}
 &   & (\uAssocL \circ \uAssocR)(x) \\
 & = & \uAssocL(\uAssocR(\rgt(c))) \\
 & = & \uAssocL(\rgt(\rgt(c))) \\
 & = & \rgt(c) \\
 & = & x,
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

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
>   => a -> b -> c -> Test (Either a (Either b c) -> Bool)
> _test_uassocR_uassocL _ _ _ =
>   testName "uassocR . uassocL == id" $
>   \x -> eq (uassocR (uassocL x)) x
> 
> 
> _test_uassocL_uassocR :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (Either (Either a b) c -> Bool)
> _test_uassocL_uassocR _ _ _ =
>   testName "uassocL . uassocR == id" $
>   \x -> eq (uassocL (uassocR x)) x

</p></div>
</div>

We also define some helper functions which detect whether an element of $A + B$ is a $\lft$ or a $\rgt$.

<div class="result">
<div class="defn">
Let $A$ and $B$ be sets. We define $\isLft : A + B \rightarrow \bool$ by $$\isLft = \either(\const(\btrue),\const(\bfalse))$$ and $\isRgt : A + B \rightarrow \bool$ by $$\isRgt = \either(\const(\bfalse),\const(\btrue)).$$

In Haskell:

> isLft :: Either a b -> Bool
> isLft = either (const True) (const False)
> 
> isRgt :: Either a b -> Bool
> isRgt = either (const False) (const True)

</div>
</div>

Now $\isLft$ and $\isRgt$ have some nice properties.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then we have the following for all $a \in A$ and $b \in B$.

1. $\isLft(\lft(a)) = \btrue$.
2. $\isLft(\rgt(b)) = \bfalse$.
3. $\isRgt(\lft(a)) = \bfalse$.
4. $\isRgt(\rgt(b)) = \btrue$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \isLft(\lft(a)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\lft(a)) \\
 & = & \const(\btrue)(a) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \isLft(\rgt(b)) \\
 & = & \either(\const(\btrue),\const(\bfalse))(\rgt(b)) \\
 & = & \const(\bfalse)(b) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \isRgt(\lft(a)) \\
 & = & \either(\const(\bfalse),\const(\btrue))(\lft(a)) \\
 & = & \const(\bfalse)(a) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \isRgt(\rgt(b)) \\
 & = & \either(\const(\bfalse),\const(\btrue))(\rgt(b)) \\
 & = & \const(\btrue)(b) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_isLft_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_isLft_lft _ y =
>   testName "isLft(lft(a)) == true" $
>   \a -> eq (isLft ((lft a) `withTypeOf` (rgt y))) True
> 
> 
> _test_isLft_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_isLft_rgt x _ =
>   testName "isLft(rgt(b)) == false" $
>   \b -> eq (isLft ((rgt b) `withTypeOf` (lft x))) False
> 
> 
> _test_isRgt_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_isRgt_lft _ y =
>   testName "isRgt(lft(a)) == false" $
>   \a -> eq (isRgt ((lft a) `withTypeOf` (rgt y))) False
> 
> 
> _test_isRgt_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_isRgt_rgt x _ =
>   testName "isRgt(rgt(b)) == true" $
>   \b -> eq (isRgt ((rgt b) `withTypeOf` (lft x))) True

</p></div>
</div>


Testing
-------

The suite:

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
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
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


And ``main``:

> main_disjoint_union :: IO ()
> main_disjoint_union = _test_disjoint_union True True True 20 100
