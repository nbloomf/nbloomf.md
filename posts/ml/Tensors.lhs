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
> import Numeric.AD.Mode.Reverse
> 
> import Indices

In the last post, we defined two algebras whose elements represent the possible sizes of multidimensional arrays and possible indices into multidimensional arrays, respectively. We did this in such a way that the possible indices into an array with (vector space) dimension $k$ can be mapped to $\{0,1, \ldots, k-1\}$ in a canonical way. With this in hand, we can define a <em>tensor</em> of size $s \in \mathbb{S}$ as a mapping from the indices of $s$ to $\mathbb{R}$. And thanks to the canonical mapping, we can implement our tensors in memory using a linear array.

> data Tensor r
>   = T Size (Array Integer r)
>   deriving (Eq, Show)

We'll also define some helper functions to make building tensors more convenient. First, one allowing us to specify a size and a map from indices to $\mathbb{R}$s. (This is really the only constructor we need.)

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

Building tensors is great, but we'd also like to be able to query them; ``at`` is the simplest such function.

> at :: Tensor r -> Index -> r
> at (T s a) t = if t `isIndexOf` s
>   then a ! (flatten s t)
>   else error "incompatible index"

With ``tensor`` and ``at`` we can manipulate tensors in more interesting ways. ``pointwise`` applies a given function to each entry of a tensor.

> pointwise :: (r -> s) -> Tensor r -> Tensor s
> pointwise f a@(T u _) = tensor u (\i -> f (a`at`i))

And ``pointwise`` generalizes; ``pointwise2`` applies a function of two arguments two the entries of two tensors.

> pointwise2 :: (r -> s -> t) -> Tensor r -> Tensor s -> Tensor t
> pointwise2 f a@(T u _) b@(T v _) =
>   if u == v
>     then tensor u (\i -> f (a`at`i) (b`at`i))
>     else error "pointwise2 requires tensors of the same size."


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

> dot :: (Num r) => Tensor r -> Tensor r -> r
> dot a@(T u _) b@(T v _) =
>   if u == v
>     then sum [ (a`at`i)*(b`at`i) | i <- indicesOf u ]
>     else error "tensors must have the same size."

> normSquared :: (Num r) => Tensor r -> r
> normSquared a = dot a a


Structural Arithmetic
---------------------

> projL, projR :: Index -> Tensor r -> Tensor r
> 
> projL i a@(T (u :* v) _) = if (i `isIndexOf` u)
>   then tensor v (\j -> a `at` (i :& j))
>   else error "index and size not compatible."
> 
> projR j a@(T (u :* v) _) = if (j `isIndexOf` v)
>   then tensor u (\i -> a `at` (i :& j))
>   else error "index and size not compatible."

> summandL, summandR :: Tensor r -> Tensor r
> 
> summandL a@(T (u :+ _) _) =
>   tensor u (\i -> a `at` (L i))
> 
> summandR a@(T (_ :+ v) _) =
>   tensor v (\j -> a `at` (R j))


> (~-~) :: Tensor r -> Tensor r -> Tensor r
> (~-~) a@(T (u :* h) _) b@(T (v :* k) _) =
>   if h == k
>     then tensor ((u :+ v) :* k)
>       (\ (t :& k) -> case t of
>         L i -> a `at` (i :& k)
>         R j -> b `at` (j :& k)
>       )
>     else error "size mismatch"
> 
> (~|~) :: Tensor r -> Tensor r -> Tensor r
> (~|~) a@(T (h :* u) _) b@(T (k :* v) _) =
>   if h == k
>     then tensor (k :* (u :+ v))
>       (\ (k :& t) -> case t of
>         L i -> a `at` (k :& i)
>         R j -> b `at` (k :& j)
>       )
>     else error "size mismatch"

> contract :: (Num r) => Tensor r -> Tensor r -> Tensor r
> contract a@(T (m :* n) _) b@(T (u :* v) _) =
>   if u == n
>     then tensor (m*v)
>       (\ (i :& j) -> sum [ (a`at`(i :& k))*(b`at`(k :& j)) | k <- indicesOf n ])
>     else error "inner sizes must match."
> contract _ _ = error "contraction expects matrices with product sizes."

> data Model r = M
>   { paramSize   :: Size
>   , inputSize   :: Size
>   , outputSize  :: Size
>   , regularized :: [Index]
>   , function    :: Tensor r -> Tensor r -> Tensor r
>   }

> linearModel :: (Num r) => Size -> Size -> Model r
> linearModel from to = M
>   { paramSize   = (to :* from) :+ to
>   , inputSize   = from
>   , outputSize  = to
>   , regularized = map L $ indicesOf (to :* from)
>   , function    = \ m x -> (contract (summandL m) x) .+ (summandR m)
>   }

> compose :: Model r -> Model r -> Model r
> compose mB mA =
>   if (inputSize mB) == (outputSize mA)
>     then M
>       { paramSize   = (paramSize mB) :+ (paramSize mA)
>       , inputSize   = inputSize mA
>       , outputSize  = outputSize mB
>       , regularized = (map L $ regularized mB) ++ (map R $ regularized mA)
>       , function    = \ p -> (function mB (summandL p)) . (function mA (summandR p))
>       }
>     else error "size mismatch."

> data CostFunction r
>   = CF ([(Tensor r, Tensor r)] -> Model r -> Tensor r -> r)

> sumSquaredError :: (Real r, Fractional r) => CostFunction r
> sumSquaredError = CF $ \ trainingData model parameters ->
>   let
>     m = fromIntegral $ length trainingData
>     f = function model
>     k (x,y) = normSquared ((f parameters x) .- y)
>   in
>     (sum $ map k trainingData) / (2*m)

> regularize :: (Real r, Fractional r) => r -> CostFunction r -> CostFunction r
> regularize lambda (CF f) = CF $ \ trainingData model parameters ->
>   let
>     reg = sum [ (parameters `at` i)^2 | i <- regularized model ]
>     m = fromIntegral $ length $ regularized model
>   in
>     (f trainingData model parameters) + (lambda * reg / m)

> unroll :: Size -> (Tensor r -> r) -> [r] -> r
> unroll s f xs = f (tensor s (\i -> xs !! (fromIntegral $ flatten s i)))

> func :: [(Tensor r, Tensor r)] -> Model r -> CostFunction r -> Tensor r
> func trainingData model = undefined


> foo :: (Num a) => [a] -> a
> foo xs = sum $ map (\z -> z*z) xs

> bar :: [Double] -> [Double]
> bar = grad foo
