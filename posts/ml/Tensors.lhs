---
title: Tensors
author: nbloomf
date: 2017-10-13
tags: ml, literate-haskell
---

First some boilerplate.

> module Tensors where
> 
> import Data.Array
> import Text.PrettyPrint
> import Test.QuickCheck
> 
> import Indices

In the last post, we defined two algebras whose elements represent the possible sizes of multidimensional arrays and possible indices into multidimensional arrays, respectively. We did this in such a way that the possible indices into an array with (vector space) dimension $k$ can be mapped to $\{0,1, \ldots, k-1\}$ in a canonical way. With this in hand, we can define a <em>tensor</em> of size $s \in \mathbb{S}$ as a mapping from the indices of $s$ to $\mathbb{R}$. And thanks to the canonical mapping, we can implement our tensors in memory using a linear array. In math notation, we will identify each $s \in \mathbb{S}$ with it's indices, and think of tensors as elements of $\mathbb{R}^s$ (that is, functions from indices to real numbers).

> data Tensor r = T
>   { size :: Size
>   , elts :: (Array Integer r)
>   } deriving Eq

To retrieve the entry of a tensor at a given index, we evaluate the tensor as a function. We'll call this special case of function application ``at``. So in math notation, we'd write $\mathsf{at}(A,i) = A(i)$ or $A_i$.

> at :: Tensor r -> Index -> r
> at (T s a) t = if t `isIndexOf` s
>   then a ! (flatten s t)
>   else error "incompatible index"

We'll also define some helper functions to make building tensors more convenient. First, one allowing us to specify a size and a map from indices to $\mathbb{R}$s. (This is really the only constructor we need.) In math notation, $\mathsf{tensor}$ is like defining a tensor $M$ by saying $A \in \mathbb{R}^s$ and $A(i) = f(i)$ for some function $f$.

> tensor :: Size -> (Index -> r) -> Tensor r
> tensor s f = T s (array (0,(dimOf s)-1) entries)
>   where
>     entries = [(flatten s t, f t) | t <- indicesOf s]

For instance, a <em>uniform</em> tensor has the same value at each index.

> uniform :: Size -> r -> Tensor r
> uniform s x = tensor s (\_ -> x)
> 
> ones, zeros :: (Num r) => Size -> Tensor r
> ones s = uniform s 1
> zeros s = uniform s 0

While we're at it, the identity matrix:

> idMat :: (Num r) => Size -> Tensor r
> idMat n = tensor (n :* n) (\ (i :& j) -> if i==j then 1 else 0)

The downside of defining our tensors recursively is that it's less clear what the index of a given entry is. To help out with this, we'll define two helpers: ``indexOf``, that defines a tensor of a given size whose entries are equal to their indices, and ``orderOf``, that shows how the entries of a tensor are linearized internally.

> indexOf :: Size -> Tensor Index
> indexOf s = tensor s id
> 
> orderOf :: Size -> Tensor Integer
> orderOf s = tensor s (flatten s)

For example, here are three different views of a size $3 \otimes 3$ tensor.

```haskell
$> ones (3*3)
1 1 1
1 1 1
1 1 1
$> indexOf (3*3)
(0,0) (0,1) (0,2)
(1,0) (1,1) (1,2)
(2,0) (2,1) (2,2)
$> orderOf (3*3)
0 3 6
1 4 7
2 5 8
```

With ``tensor`` and ``at`` we can manipulate tensors in more interesting ways. ``pointwise`` applies a given function to each entry of a tensor.

> pointwise :: (r -> s) -> Tensor r -> Tensor s
> pointwise f a@(T u _) = tensor u (\i -> f (a`at`i))

In math notation, $$\mathsf{pointwise}(f)(A)_i = f(A_i).$$ And ``pointwise`` generalizes; ``pointwise2`` applies a function of two arguments two the entries of two tensors.

> pointwise2 :: (r -> s -> t) -> Tensor r -> Tensor s -> Tensor t
> pointwise2 f a@(T u _) b@(T v _) =
>   if u == v
>     then tensor u (\i -> f (a`at`i) (b`at`i))
>     else error "pointwise2 requires tensors of the same size."

In math notation, $\mathsf{pointwise2}(f)(A)(B)_i = f(A_i,B_i)$.

We'd also like to extract all entries from a tensor as a list.

> entries :: Tensor r -> [r]
> entries a@(T s _) = [ a`at`i | i <- indicesOf s ]

And with the list of entries in hand, we can fold them.

> tfold :: (r -> r -> r) -> Tensor r -> r
> tfold f t = case entries t of
>   [] -> error "tfold: empty tensor"
>   xs -> foldr1 f xs

For instance, we can use ``tfold`` to find the sum or max of the entries of a tensor.

> esum :: (Num r) => Tensor r -> r
> esum = tfold (+)
> 
> emax :: (Ord r) => Tensor r -> r
> emax = tfold max

I'll wrap up with a constructor for the size 1 tensor.

> cell :: r -> Tensor r
> cell r = tensor 1 (\_ -> r)


Vector Arithmetic
-----------------

Tensors are vectors, so they should have the usual vector operations of plus, negate, and scale.

> (.+) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> (.+) = pointwise2 (+)
> 
> neg :: (Num r) => Tensor r -> Tensor r
> neg = pointwise negate
> 
> (.-) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> a .- b = a .+ (neg b)
> 
> (.@) :: (Num r) => r -> Tensor r -> Tensor r
> r .@ a = pointwise (r*) a

While we're at it, a summation operator for tensors.

> tsum :: (Num r, Foldable t) => t (Tensor r) -> Tensor r
> tsum = foldr1 (.+)

The Hadamard or entrywise product is also handy.

> (.*) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> (.*) = pointwise2 (*)

Thinking of tensors as vectors, we can dot them together in the usual way.

> dot :: (Num r) => Tensor r -> Tensor r -> r
> dot a@(T u _) b@(T v _) =
>   if u == v
>     then sum [ (a`at`i)*(b`at`i) | i <- indicesOf u ]
>     else error "tensors must have the same size."

In math notation, if $A,B \in \mathbb{R}^s$, $$\mathsf{dot}(A,B) = \sum_{i \in s} A_i B_i.$$ The 'dot square' of a tensor will also be handy later.

> normSquared :: (Num r) => Tensor r -> r
> normSquared a = dot a a


Structural Arithmetic
---------------------

Now we'll define some structural operators on tensors; these are functions that manipulate the size of a tensor, or combine tensors into more complicated ones, or extract subparts.

> oplus :: Tensor r -> Tensor r -> Tensor r
> oplus a@(T u _) b@(T v _) = tensor (u :+ v) $
>   \k -> case k of
>     L i -> a `at` i
>     R j -> b `at` j

Next we have projection operators, which take a tensor in $\mathbb{R}^{s \otimes t}$ and fix one of the index components. In the usual matrix language, projection would extract one row or one column of a matrix. There are two of these, with the following signature.

> projR, projL :: Index -> Tensor r -> Tensor r

In math notation we have $\mathsf{projR} : s \rightarrow \mathbb{R}^{t \otimes s} \rightarrow \mathbb{R}^t$ given by $\mathsf{projL}(i,A)_j = A_{i \& j}$, and $\mathsf{projL}$ is similar.

> projR i a@(T (u :* v) _) = if (i `isIndexOf` u)
>   then tensor v (\j -> a `at` (i :& j))
>   else error "in projR: index and size not compatible."
> 
> projL j a@(T (u :* v) _) = if (j `isIndexOf` v)
>   then tensor u (\i -> a `at` (i :& j))
>   else error "in projL: index and size not compatible."

Similarly, we can extract "terms" from a summand tensor using functions with the following signature.

> termL, termR :: Tensor r -> Tensor r

In math notation we have $\mathsf{termL} : \mathbb{R}^{s \oplus t} \rightarrow \mathbb{R}^s$ given by $\mathsf{termL}(A)_i = A_{\mathsf{l}(i)}$, and $\mathsf{termR}$ is similar.

> termL a@(T (u :+ _) _) =
>   tensor u (\i -> a `at` (L i))
> 
> termR a@(T (_ :+ v) _) =
>   tensor v (\j -> a `at` (R j))

Now $\mathbb{R}^{u \otimes v}$ and $\mathbb{R}^{v \otimes u}$ are not equal, but they are canonically isomorphic; likewise $\mathbb{R}^{u \oplus v}$ and $\mathbb{R}^{v \oplus u}$.

> comm :: Tensor r -> Tensor r
> 
> comm a@(T (u :* v) _) = tensor (v :* u) $
>   \(j :& i) -> a `at` (i :& j)
> 
> comm a@(T (u :+ v) _) = tensor (v :+ u) $
>   \k -> case k of
>     L i -> a `at` R i
>     R i -> a `at` L i
> 
> comm _ = error "comm"

Similarly, $\mathbb{R}^{u \otimes (v \otimes w)}$ and $\mathbb{R}^{(u \otimes v) \otimes w}$ are canonically isomorphic, and likewise for $\oplus$.

> assocL, assocR :: Tensor r -> Tensor r
> 
> assocL a@(T (u :* (v :* w)) _) = tensor ((u :* v) :* w) $
>   \((i :& j) :& k) -> a `at` (i :& (j :& k))
> 
> assocL a@(T (u :+ (v :+ w)) _) = tensor ((u :+ v) :+ w) $
>   \k -> case k of
>     L (L i) -> a `at` L i
>     L (R i) -> a `at` R (L i)
>     R i     -> a `at` R (R i)
> 
> assocL _ = error "assocL"
> 
> assocR a@(T ((u :* v) :* w) _) = tensor (u :* (v :* w)) $
>   \(i :& (j :& k)) -> a `at` ((i :& j) :& k)
> 
> assocR a@(T ((u :+ v) :+ w) _) = tensor (u :+ (v :+ w)) $
>   \k -> case k of
>     R (R i) -> a `at` R i
>     R (L i) -> a `at` L (R i)
>     L i     -> a `at` L (L i)
> 
> assocR _ = error "assocR"

Recall that the $\otimes$ operator in $\mathbb{S}$ does not really distribute over $\oplus$, so for example $a \otimes (b \oplus c)$ and $(a \otimes b) \oplus (a \otimes c)$ are distinct tensor sizes, and meanwhile we have $$\mathbb{R}^{(a \otimes b) \oplus (a \otimes c)} \cong \mathbb{R}^{a \otimes b} \times \mathbb{R}^{a \otimes c}.$$ We'll define a couple of operators to canonically "undistribute" $\otimes$ over $\oplus$.

> unDistL, (~-~) :: Tensor r -> Tensor r -> Tensor r
> unDistL a@(T (u :* h) _) b@(T (v :* k) _) =
>   if h == k
>     then tensor ((u :+ v) :* k)
>       (\ (t :& k) -> case t of
>         L i -> a `at` (i :& k)
>         R j -> b `at` (j :& k)
>       )
>     else error "size mismatch"
> 
> (~-~) = unDistL
> 
> unDistR, (~|~) :: Tensor r -> Tensor r -> Tensor r
> unDistR a@(T (h :* u) _) b@(T (k :* v) _) =
>   if h == k
>     then tensor (k :* (u :+ v))
>       (\ (k :& t) -> case t of
>         L i -> a `at` (k :& i)
>         R j -> b `at` (k :& j)
>       )
>     else error "size mismatch"
> 
> (~|~) = unDistR

We give ``unDistL`` and ``unDistR`` symbolic synonyms, meant to evoke what they do on matrices. ``unDistL`` concatenates matrices vertically, and ``unDistR`` concatenates them horizontally.

> contract :: (Num r) => Tensor r -> Tensor r -> Tensor r
> contract a@(T (m :* n) _) b@(T (u :* v) _) =
>   if u == n
>     then tensor (m*v)
>       (\ (i :& j) -> sum
>         [ (a`at`(i :& k))*(b`at`(k :& j)) | k <- indicesOf n ])
>     else error "inner sizes must match."
> contract _ _ = error "contraction expects matrices with product sizes."

> common :: (Eq a) => [a] -> Maybe a
> common []     = Nothing
> common (x:xs) = if not $ any (/= x) xs
>   then Just x
>   else Nothing

> mapL :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> mapL f a@(T (u :* v) _) = tensor (w :* v) $
>   \(i :& j) -> f (projL j a) `at` i
>   where
>     w = case common [ size $ f (projL j a) | j <- indicesOf v ] of
>       Just k -> k
>       Nothing -> error "mapL"
> 
> mapL f a@(T (u :+ v) _) =
>   let
>     m = f (termL a)
>     w = size m
>   in
>     tensor (w :+ v) $
>       \k -> case k of
>         L i -> m `at` i
>         R i -> a `at` (R i)

> mapR :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> mapR f a@(T (u :* v) _) = tensor (u :* w) $
>   \(i :& j) -> f (projR i a) `at` j
>   where
>     w = case common [ size $ f (projR i a) | i <- indicesOf u ] of
>       Just k -> k
>       Nothing -> error "mapR"
> 
> mapR f a@(T (u :+ v) _) =
>   let
>     m = f (termR a)
>     w = size m
>   in
>     tensor (w :+ v) $
>       \k -> case k of
>         R i -> m `at` i
>         L i -> a `at` (L i)


Pretty Printing
---------------

We'll end this post with the ``Show`` instance for tensors; we'll build it on top of the pretty printing [combinator library](https://hackage.haskell.org/package/pretty-1.1.3.5) by John Hughes and Simon Peyton Jones. (The original [paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.38.8777) on that library is a nice case study in DSL design.)

First we convert a tensor of strings to a ``Doc`` (in the pretty printer parlance), doing more or less the obvious thing.

> toDoc :: Tensor String -> Doc
> toDoc a@(T s _) =
>   case s of
>     Size k -> hsep $ map text [ a`at`i | i <- indicesOf s ]
>     u :+ v -> (toDoc $ termL a) $$ (toDoc $ termR a)
>     u :* v -> vcat [
>                 hsep [
>                   text $ a `at` (i :& j)
>                 | j <- indicesOf v ]
>               | i <- indicesOf u ]

To actually show the tensor, we show the entries (pointwise) and pad to the maximum entry width (so the cells line up), then show the corresponding ``Doc``.

> instance (Show r) => Show (Tensor r) where
>   show a =
>     let
>       cellWidth = maximum $ map (length . show) $ entries a
>       m = pointwise (padLeft cellWidth . show) a
>     in
>       render $ toDoc m
>     where
>       -- left-pad a string with spaces to a given length
>       padLeft :: Int -> String -> String
>       padLeft k = reverse . take k . (++ (repeat ' ')) . reverse

This method for displaying tensors is not perfect, but it has the advantage of being simple and doing mostly the right thing in the most common cases of $k$ and $m \otimes n$ tensors (i.e. matrices). Apropos of nothing: further support for this method is that tensors with shape $k_1 \oplus k_2 \oplus \cdots \oplus k_n$ look like [Young tableaux](https://en.wikipedia.org/wiki/Young_tableau).


Tests
-----

In future posts we'll be writing tests involving tensors, so I'll put an ``Arbitrary`` instance here.

> instance (Arbitrary r) => Arbitrary (Tensor r) where
>   arbitrary = arbitrary >>= arbTensor
> 
> arbTensor :: (Arbitrary r) => Size -> Gen (Tensor r)
> arbTensor s = do
>   as <- vectorOf (fromIntegral $ dimOf s) arbitrary
>   return $ tensor s (\i -> as !! (fromIntegral $ flatten s i))
> 
> arbMatrix :: (Arbitrary r) => Integer -> Integer -> Gen (Tensor r)
> arbMatrix r c = arbTensor ((Size r) :* (Size c))
