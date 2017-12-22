---
title: Disjoint Unions
author: nbloomf
date: 2017-12-21
tags: literate-haskell, arithmetic-made-difficult
slug: disjoint-unions
---

> {-# LANGUAGE ScopedTypeVariables #-}
> module DisjointUnions
>   ( lft, rgt, either, uswap, upair
>   , _test_disjoint_union, main_disjoint_union
>   ) where
> 
> import Prelude ()
> import Booleans

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

> _test_swap_lft :: (Equal a, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_swap_lft _ y =
>   testName "swap(left(a)) == right(a)" $
>   \a -> eq
>     (uswap (lft a))
>     ((rgt a) `withTypeOf` (lft y))
> 
> 
> _test_swap_rgt :: (Equal a, Equal b)
>   => a -> b -> Test (b -> Bool)
> _test_swap_rgt x _ =
>   testName "swap(right(a)) == left(a)" $
>   \b -> eq
>     (uswap (rgt b))
>     ((lft b) `withTypeOf` (rgt x))
> 
> 
> _test_swap_swap :: (Equal a, Equal b)
>   => a -> b -> Test (Either a b -> Bool)
> _test_swap_swap _ _ =
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

> _test_pair_lft :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> a -> Bool)
> _test_pair_lft _ y =
>   testName "upair(f,g)(lft(a)) == lft(f(a))" $
>   \f g a -> eq
>     (upair f g ((lft a) `withTypeOf` (rgt y)))
>     ((lft (f a)) `withTypeOf` (rgt y))
> 
> 
> _test_pair_rgt :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> b -> Bool)
> _test_pair_rgt x _ =
>   testName "upair(f,g)(rgt(b)) == rgt(g(b))" $
>   \f g b -> eq
>     (upair f g ((rgt b) `withTypeOf` (lft x)))
>     ((rgt (g b)) `withTypeOf` (lft x))
> 
> 
> _test_pair_pair :: (Equal a, Equal b)
>   => a -> b
>   -> Test ((a -> a) -> (b -> b) -> (a -> a) -> (b -> b) -> Either a b -> Bool)
> _test_pair_pair _ _ =
>   testName "upair(f,g) . upair(h,k) == upair(f . h, g . k)" $
>   \f g h k x ->
>     eq
>       (upair f g (upair h k x))
>       (upair (f . h) (g . k) x)

</p></div>
</div>


Testing
-------

The suite:

> _test_disjoint_union
>   :: ( Show a, Show b, Show c
>      , Equal a, Equal b, Equal c
>      , Arbitrary a, Arbitrary b, Arbitrary c
>      , CoArbitrary a, CoArbitrary b )
>   => a -> b -> c -> Int -> Int -> IO ()
> _test_disjoint_union a b c size num = do
>   testLabel "Disjoint Union"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_either_lft_rgt a b)
>   runTest args (_test_swap_lft a b)
>   runTest args (_test_swap_rgt a b)
>   runTest args (_test_swap_swap a b)
>   runTest args (_test_pair_lft a b)
>   runTest args (_test_pair_rgt a b)
>   runTest args (_test_pair_pair a b)


And ``main``:

> main_disjoint_union :: IO ()
> main_disjoint_union = _test_disjoint_union True True True 20 100
