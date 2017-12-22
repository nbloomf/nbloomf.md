---
title: Tuples
author: nbloomf
date: 2014-04-02
tags: arithmetic-made-difficult, literate-haskell
slug: tuples
---

> module Tuples
>   ( fst, snd, dup, tswap, pair, assocL, assocR
>   , _test_tuple, main_tuple
>   ) where
> 
> import Prelude ()
> import Booleans

Today we'll establish a few basic utility functions on *tuples*. First, recall some definitions.

<div class="result">
<div class="defn">
Let $A$ and $B$ be sets. There is a set $A \times B$ together with two functions $\fst : A \times B \rightarrow A$ and $\snd : A \times B \rightarrow B$ having the property that if $X$ is a set and $\sigma : X \rightarrow A$ and $\tau : X \rightarrow B$ functions then there is a unique map $\Theta : X \rightarrow A \times B$ such that $\fst \circ \Theta = \sigma$ and $\snd \circ \Theta = \tau$. That is, there is a unique $\Theta$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
X @= X @= X \\
@V{\sigma}VV @VV{\Theta}V @VV{\tau}V \\
A @<<{\fst}< A \times B @>>{\snd}> B
\end{CD}$$

We will denote this unique $\Theta : X \rightarrow A \times B$ by $\dup(\sigma,\tau)$.

More concretely, if $f : X \rightarrow A \times B$ such that $\fst(f(x)) = \sigma(x)$ and $\snd(f(x)) = \tau(x)$ for all $x \in X$, then $f = \dup(\sigma,\tau)$.
</div>
</div>

Now $A \times B$ uniquely represents all possible pairs of elements of $A$ and $B$ in a precise sense.

<div class="result">
<div class="thm">
Let $A$ and $B$ be sets.

1. If $a \in A$ and $b \in B$, then there exists $w \in A \times B$ such that $\fst(w) = a$ and $\snd(w) = b$.
2. If $x,y \in A \times B$ such that $\fst(x) = \fst(y)$ and $\snd(x) = \snd(y)$, then $x = y$.
</div>

<div class="proof"><p>
1. Let $a \in A$ and $b \in B$. Define $\sigma : \{\ast\} \rightarrow A$ by $\sigma(\ast) = a$, and $\tau : \{\ast\} \rightarrow B$ by $\tau(\ast) = b$. Let $\Theta = \dup(\sigma,\tau)$, and consider $w = \Theta(\ast) \in A \times B$. In particular, note that
$$\begin{eqnarray*}
 &   & \fst(w) \\
 & = & \fst(\Theta(\ast)) \\
 & = & (\fst \circ \Theta)(\ast) \\
 & = & \sigma(\ast) \\
 & = & a
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(w) \\
 & = & \snd(\Theta(\ast)) \\
 & = & (\snd \circ \Theta)(\ast) \\
 & = & \tau(\ast) \\
 & = & b
\end{eqnarray*}$$
as needed.
2. Say $a = \fst(x) = \fst(y)$ and $b = \snd(x) = \snd(y)$. Define $\sigma : \{\ast\} \rightarrow A$ by $\sigma(\ast) = a$, and $\tau : \{\ast\} \rightarrow B$ by $\tau(\ast) = b$. Now consider $f,g : \{\ast\} \rightarrow A \times B$ given by $f(\ast) = x$ and $g(\ast) = y$. Note that
$$\begin{eqnarray*}
 &   & \fst(f(\ast)) \\
 & = & \fst(x) \\
 & = & a \\
 & = & \fst(y) \\
 & = & \fst(g(\ast))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \snd(f(\ast)) \\
 & = & \snd(x) \\
 & = & b \\
 & = & \snd(y) \\
 & = & \snd(g(\ast)).
\end{eqnarray*}$$
In particular, we have $$f = \dup(\sigma,\tau) = g$$ and thus $$x = f(\ast) = g(\ast) = y$$ as claimed.
</p></div>
</div>

In Haskell we can model $A \times B$ with the tuple type ``(a,b)``, and the maps in the universal property like so.

> fst :: (a,b) -> a
> fst (a,_) = a
> 
> snd :: (a,b) -> b
> snd (_,b) = b
> 
> dup :: (x -> a) -> (x -> b) -> x -> (a,b)
> dup f g x = (f x, g x)

For example, $\id_{A \times B}$ is a $\dup$.

<div class="result">
<div class="thm"><p>
Provided the types match up, we have $$\dup(\fst,\snd) = \id_{A \times B}.$$
</p></div>

<div class="proof"><p>
Note that for all $(a,b) \in A \times B$ we have
$$\begin{eqnarray*}
 &   & \dup(\fst,\snd)(a,b) \\
 & = & (\fst(a,b),\snd(a,b)) \\
 & = & (a,b)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_dup_fst_snd :: (Equal a, Equal b)
>   => a -> b -> Test ((a,b) -> Bool)
> _test_dup_fst_snd _ _ =
>   testName "dup(fst,snd) == id" $
>   \x -> eq (dup fst snd x) x

</p></div>
</div>

We define $\tSwap$ on tuples like so.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. We define $\tSwap : A \times B \rightarrow B \times A$ by $$\tSwap = \dup(\snd,\fst).$$

In Haskell,

> tswap :: (a,b) -> (b,a)
> tswap = dup snd fst

</p></div>
</div>

Elements of $A \times B$ act like "ordered pairs", and $\tSwap$ effectively reverses the order of the pair.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then we have the following.

1. $\tSwap(a,b) = (b,a)$.
2. $\tSwap(\tSwap(a,b)) = (a,b)$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \tSwap(a,b) \\
 & = & \dup(\snd,\fst)(a,b) \\
 & = & (\snd(a,b),\fst(a,b)) \\
 & = & (b,a)
\end{eqnarray*}$$
as claimed.
2. Note that for all $(a,b) \in A \times B$ we have
$$\begin{eqnarray*}
 &   & \tSwap(\tSwap(a,b)) \\
 & = & \tSwap(b,a) \\
 & = & (a,b)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_tswap_entries :: (Equal a, Equal b)
>   => a -> b -> Test ((a,b) -> Bool)
> _test_tswap_entries _ _ =
>   testName "tswap(a,b) == (b,a)" $
>   \(a,b) -> eq (tswap (a,b)) (b,a)
> 
> 
> _test_tswap_tswap :: (Equal a, Equal b)
>   => a -> b -> Test ((a,b) -> Bool)
> _test_tswap_tswap _ _ =
>   testName "tswap(tswap(x)) == x" $
>   \x -> eq (tswap (tswap x)) x

</p></div>
</div>

Next, the utility $\tPair$ facilitates defining functions from one tuple to another.

<div class="result">
<div class="defn"><p>
Let $A$, $B$, $U$, and $V$ be sets. We define $\tPair : U^A \times V^B \rightarrow (U \times V)^{A \times B}$ by $$\tPair(f,g) = \dup(f \circ \fst, g \circ \snd).$$

In Haskell:

> pair :: (a -> u) -> (b -> v) -> (a,b) -> (u,v)
> pair f g = dup (f . fst) (g . snd)

</p></div>
</div>

$\tPair$ has some nice properties.

<div class="result">
<div class="thm">
For all $f$, $g$, $h$, $k$, $a$, and $b$ we have the following.

1. $\tPair(f,g)(a,b) = (f(a),g(b))$.
2. $\tPair(f,g) \circ \tPair(h,k) = \tPair(f \circ h, g \circ k)$.
</div>

<div class="proof"><p>
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
</p></div>

<div class="test"><p>

> _test_pair_apply :: (Equal a, Equal b)
>   => a -> b -> Test ((a -> a) -> (b -> b) -> (a,b) -> Bool)
> _test_pair_apply _ _ =
>   testName "pair(f,g)(a,b) == (f(a),g(b))" $
>   \f g (a,b) -> eq (pair f g (a,b)) (f a, g b)
> 
> 
> _test_pair_pair :: (Equal a, Equal b)
>   => a -> b
>   -> Test ((a -> a) -> (b -> b) -> (a -> a) -> (b -> b) -> (a,b) -> Bool)
> _test_pair_pair _ _ =
>   testName "pair(f,g) o pair(h,k) == pair(f o h, g o k)" $
>   \f g h k x ->
>     eq
>       (pair f g (pair h k x))
>       (pair (f . h) (g . k) x)

</p></div>
</div>

Finally, note that although as sets $A \times (B \times C)$ and $(A \times B) \times C$ cannot possibly be equal to each other in general, they are naturally isomorphic via $\tAssocL$ and $\tAssocR$.

<div class="result">
<div class="defn">
Let $A$, $B$, and $C$ be sets. We define $\tAssocL : A \times (B \times C) \rightarrow (A \times B) \times C$ by $$\tAssocL = \dup(\dup(\fst, \fst \circ \snd), \snd \circ \snd)$$ and define $\tAssocR : (A \times B) \times C \rightarrow A \times (B \times C)$ by $$\tAssocR = \dup(\fst \circ \fst, \dup(\snd \circ \fst, \snd)).$$

In Haskell:

> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL = dup (dup fst (fst . snd)) (snd . snd)
> 
> assocR :: ((a,b),c) -> (a,(b,c))
> assocR = dup (fst . fst) (dup (snd . fst) snd)

</div>
</div>

Now $\tAssocL$ and $\tAssocR$ have some nice properties.

<div class="result">
<div class="thm"><p>
The following hold whenever everything has the appropriate type.

1. $\tAssocL(a,(b,c)) = ((a,b),c)$.
2. $\tAssocR((a,b),c) = (a,(b,c))$.
3. $\tAssocR \circ \tAssocL = \id$.
4. $\tAssocL \circ \tAssocR = \id$.
</p></div>

<div class="proof"><p>
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
</p></div>

<div class="test"><p>

> _test_assocL_entries :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> b -> c -> Bool)
> _test_assocL_entries _ _ _ =
>   testName "assocL(a,(b,c)) == ((a,b),c)" $
>   \a b c -> eq (assocL (a,(b,c))) ((a,b),c)
> 
> 
> _test_assocR_entries :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (a -> b -> c -> Bool)
> _test_assocR_entries _ _ _ =
>   testName "assocR((a,b),c) == (a,(b,c))" $
>   \a b c -> eq (assocR ((a,b),c)) (a,(b,c))
> 
> 
> _test_assocL_assocR :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test (((a,b),c) -> Bool)
> _test_assocL_assocR _ _ _ =
>   testName "assocL . assocR == id" $
>   \x -> eq (assocL (assocR x)) x
> 
> 
> _test_assocR_assocL :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> Test ((a,(b,c)) -> Bool)
> _test_assocR_assocL _ _ _ =
>   testName "assocR . assocL == id" $
>   \x -> eq (assocR (assocL x)) x

</p></div>
</div>


Testing
-------

The suite:

> _test_tuple
>   :: ( Show a, Show b, Show c
>      , Equal a, Equal b, Equal c
>      , Arbitrary a, Arbitrary b, Arbitrary c
>      , CoArbitrary a, CoArbitrary b )
>   => a -> b -> c -> Int -> Int -> IO ()
> _test_tuple a b c size num = do
>   testLabel "Tuple"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_dup_fst_snd a b)
> 
>   runTest args (_test_tswap_entries a b)
>   runTest args (_test_tswap_tswap a b)
> 
>   runTest args (_test_pair_apply a b)
>   runTest args (_test_pair_pair a b)
> 
>   runTest args (_test_assocL_entries a b c)
>   runTest args (_test_assocR_entries a b c)
>   runTest args (_test_assocL_assocR a b c)
>   runTest args (_test_assocR_assocL a b c)


And ``main``:

> main_tuple :: IO ()
> main_tuple = _test_tuple True True True 20 100
