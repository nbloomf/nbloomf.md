---
title: Tuples
author: nbloomf
date: 2014-04-02
tags: arithmetic-made-difficult, literate-haskell
---

> module Tuples
>   ( fst, snd, dup, swap, pair, assocL, assocR
>   , _test_tuple, main_tuple
>   ) where
> 
> import Booleans
> 
> import Prelude(Show, Int, IO, (.))
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll establish some basic utility functions on *tuples*. First, recall some definitions.

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. There is a set $A \times B$ together with two functions $\fst : A \times B \rightarrow A$ and $\snd : A \times B \rightarrow B$ having the property that if $X$ is a set and $\sigma : X \rightarrow A$ and $\tau : X \rightarrow B$ functions then there is a unique map $\Theta : X \rightarrow A \times B$ such that $\fst \circ \Theta = \sigma$ and $\snd \circ \Theta = \tau$. That is, there is a unique $\Theta$ such that the following diagram commutes.

$$\require{AMScd}
\begin{CD}
X @= X @= X\\
@V{\sigma}VV @VV{\Theta}V @VV{\tau}V \\
A @<<{\fst}< A \times B @>>{\snd}> B
\end{CD}$$

We will denote this unique $\Theta : X \rightarrow A \times B$ by $\dup(\sigma,\tau)$.
</p></div>
</div>

In Haskell we model $A \times B$ with the tuple type ``(a,b)``.

> fst :: (a,b) -> a
> fst (a,_) = a
> 
> snd :: (a,b) -> b
> snd (_,b) = b
> 
> dup :: (x -> a) -> (x -> b) -> x -> (a,b)
> dup f g x = (f x, g x)

<div class="result">
<div class="thm"><p>
Provided the types match up, we have $$\dup(\fst,\snd) = \id.$$
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
</div>

Now $\swap$ reverses the entries of a tuple:

<div class="result">
<div class="defn"><p>
Let $A$ and $B$ be sets. We define $\swap : A \times B \rightarrow B \times A$ by $$\swap = \dup(\snd,\fst).$$
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets. Then we have the following.

1. $\swap(a,b) = (b,a)$.
2. $\swap \circ \swap = \id$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \swap(a,b) \\
 & = & \dup(\snd,\fst)(a,b) \\
 & = & (\snd(a,b),\fst(a,b)) \\
 & = & (b,a)
\end{eqnarray*}$$
as claimed.
2. Note that for all $(a,b) \in A \times B$ we have
$$\begin{eqnarray*}
 &   & (\swap \circ \swap)(a,b) \\
 & = & \swap(\swap(a,b)) \\
 & = & \swap(b,a) \\
 & = & (a,b) \\
 & = & \id(a,b)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The previous result suggests a more straightforward definition for $\swap$.

> swap :: (a,b) -> (b,a)
> swap (a,b) = (b,a)

Next, the utility $\pair$ facilitates defining functions from one tuple to another.

<div class="result">
<div class="defn"><p>
Let $A$, $B$, $U$, and $V$ be sets. We define $\pair : U^A \times V^B \rightarrow (U \times V)^{A \times B}$ by $$\pair(f,g) = \dup(f \circ \fst, g \circ \snd).$$
</p></div>
</div>

<div class="result">
<div class="thm"><p>
The following hold whenever everything has the appropriate type.

1. $\pair(f,g)(a,b) = (f(a),g(b))$.
2. $\pair(f,g) \circ \pair(h,k) = \pair(f \circ h, g \circ k)$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \pair(f,g)(a,b) \\
 & = & \dup(f \circ \fst, g \circ \snd)(a,b) \\
 & = & ((f \circ \fst)(a,b),(g \circ \snd)(a,b)) \\
 & = & (f(\fst(a,b)),g(\snd(a,b))) \\
 & = & (f(a),g(b))
\end{eqnarray*}$$
as claimed.
2. Note that for all $(a,b)$ we have
$$\begin{eqnarray*}
 &   & (\pair(f,g) \circ \pair(h,k))(a,b) \\
 & = & \pair(f,g)(\pair(h,k)(a,b)) \\
 & = & \pair(f,g)(h(a),k(b)) \\
 & = & (f(h(a)),g(k(b))) \\
 & = & ((f \circ h)(a),(g \circ k)(b)) \\
 & = & \pair(f \circ h, g \circ k)(a,b)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The previous result suggests a more straightforward implementation of $\pair$:

> pair :: (a -> u) -> (b -> v) -> (a,b) -> (u,v)
> pair f g (a,b) = (f a, g b)

Finally, note that although as sets $A \times (B \times C)$ and $(A \times B) \times C$ cannot possibly be equal to each other in general, they are naturally isomorphic.

<div class="result">
<div class="defn"><p>
Let $A$, $B$, and $C$ be sets. We define $\assocL : A \times (B \times C) \rightarrow (A \times B) \times C$ by $$\assocL = \dup(\dup(\fst, \fst \circ \snd), \snd \circ \snd)$$ and define $\assocR : (A \times B) \times C \rightarrow A \times (B \times C)$ by $$\assocR = \dup(\fst \circ \fst, \dup(\snd \circ \fst, \snd)).$$
</p></div>
</div>

Now $\assocL$ and $\assocR$ have some properties:

<div class="result">
<div class="thm"><p>
The following hold whenever everything has the appropriate type.

1. $\assocL(a,(b,c)) = ((a,b),c)$.
2. $\assocR((a,b),c) = (a,(b,c))$.
3. $\assocR \circ \assocL = \id$.
4. $\assocL \circ \assocR = \id$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \assocL(a,(b,c)) \\
 & = & \dup(\dup(\fst, \fst \circ \snd),\snd \circ \snd)(a,(b,c)) \\
 & = & (\dup(\fst,\fst \circ \snd)(a,(b,c)),(\snd \circ \snd)(a,(b,c))) \\
 & = & ((\fst(a,(b,c)),\fst(\snd(a,(b,c)))),\snd(\snd(a,(b,c)))) \\
 & = & ((a,\fst(b,c)),\snd(b,c)) \\
 & = & ((a,b),c)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \assocR((a,b),c) \\
 & = & \dup(\fst \circ \fst, \dup(\snd \circ \fst, \snd))((a,b),c) \\
 & = & (\fst(\fst((a,b),c)),\dup(\snd \circ \fst, \snd)((a,b),c)) \\
 & = & (\fst(a,b),(\snd(\fst((a,b),c)),\snd((a,b),c))) \\
 & = & (a,(\snd(a,b),c)) \\
 & = & (a,(b,c))
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & (\assocR \circ \assocL)(a,(b,c)) \\
 & = & \assocR(\assocL(a,(b,c))) \\
 & = & \assocR((a,b),c) \\
 & = & (a,(b,c))
\end{eqnarray*}$$
as claimed.
4. Note that
$$\begin{eqnarray*}
 &   & (\assocL \circ \assocR)((a,b),c) \\
 & = & \assocL(\assocR((a,b),c)) \\
 & = & \assocL(a,(b,c)) \\
 & = & ((a,b),c)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The previous result suggests more straightforward implementations of $\assocL$ and $\assocR$.

> assocL :: (a,(b,c)) -> ((a,b),c)
> assocL (a,(b,c)) = ((a,b),c)
> 
> assocR :: ((a,b),c) -> (a,(b,c))
> assocR ((a,b),c) = (a,(b,c))


Testing
-------

Here are our property tests for $\bnot$:

> -- dup(fst(x),snd(x)) == x
> _test_dup_fst_snd :: (Equal a, Equal b)
>   => a -> b -> (a,b) -> Bool
> _test_dup_fst_snd _ _ x =
>   (dup fst snd x) ==== x
> 
> 
> -- dup(snd(x),fst(x)) == swap(x)
> _test_dup_snd_fst :: (Equal a, Equal b)
>   => a -> b -> (a,b) -> Bool
> _test_dup_snd_fst _ _ x =
>   (dup snd fst x) ==== (swap x)
> 
> 
> -- swap(swap(x)) == x
> _test_swap_swap :: (Equal a, Equal b)
>   => a -> b -> (a,b) -> Bool
> _test_swap_swap _ _ x =
>   (swap (swap x)) ==== x
> 
> 
> -- pair(f,g)(a,b) == (f(a),g(b))
> _test_pair_apply :: (Equal a, Equal b)
>   => a -> b -> (a -> a) -> (b -> b) -> (a,b) -> Bool
> _test_pair_apply _ _ f g (a,b) =
>   (pair f g (a,b)) ==== (f a, g b)
> 
> 
> -- pair(f,g) o pair(h,k) == pair(f o h, g o k)
> _test_pair_pair :: (Equal a, Equal b)
>   => a -> b -> (a -> a) -> (b -> b) -> (a -> a) -> (b -> b) -> (a,b) -> Bool
> _test_pair_pair _ _ f g h k (a,b) =
>   (pair f g (pair h k (a,b))) ==== (pair (f . h) (g . k) (a,b))
> 
> 
> -- assocL == dup(dup(fst, fst o snd), snd o snd)
> _test_assocL_alt :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> (a,(b,c)) -> Bool
> _test_assocL_alt _ _ _ x =
>   (assocL x) ==== (dup (dup fst (fst . snd)) (snd . snd) x)
> 
> 
> -- assocR == dup(fst o fst, dup(snd o fst, snd))
> _test_assocR_alt :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> ((a,b),c) -> Bool
> _test_assocR_alt _ _ _ x =
>   (assocR x) ==== (dup (fst . fst) (dup (snd . fst) snd) x)
> 
> 
> -- assocL o assocR == id
> _test_assocL_assocR :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> ((a,b),c) -> Bool
> _test_assocL_assocR _ _ _ x =
>   (assocL (assocR x)) ==== x
> 
> 
> -- assocR o assocL == id
> _test_assocR_assocL :: (Equal a, Equal b, Equal c)
>   => a -> b -> c -> (a,(b,c)) -> Bool
> _test_assocR_assocL _ _ _ x =
>   (assocR (assocL x)) ==== x

And the suite:

> -- run all tests for tuples
> _test_tuple :: (Show a, Show b, Show c, Equal a, Equal b, Equal c, Arbitrary a, Arbitrary b, Arbitrary c, CoArbitrary a, CoArbitrary b) => a -> b -> c -> Int -> Int -> IO ()
> _test_tuple a b c size num = do
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_dup_fst_snd a b)
>   runTest args (_test_dup_snd_fst a b)
>   runTest args (_test_swap_swap a b)
>   runTest args (_test_pair_apply a b)
>   runTest args (_test_pair_pair a b)
>   runTest args (_test_assocL_alt a b c)
>   runTest args (_test_assocR_alt a b c)
>   runTest args (_test_assocL_assocR a b c)
>   runTest args (_test_assocR_assocL a b c)


And ``main``:

> main_tuple :: IO ()
> main_tuple = _test_tuple True True True 20 100
