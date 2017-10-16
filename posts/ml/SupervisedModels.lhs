---
title: Supervised Models
author: nbloomf
date: 2017-10-14
tags: ml, literate-haskell
---

First some boilerplate.

> module SupervisedModels where
> 
> import Numeric.AD.Mode.Reverse
> 
> import Indices
> import Tensors



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
>   , function    = \ m x -> (contract (termL m) x) .+ (termR m)
>   }

> compose :: Model r -> Model r -> Model r
> compose mB mA =
>   if (inputSize mB) == (outputSize mA)
>     then M
>       { paramSize   = (paramSize mB) :+ (paramSize mA)
>       , inputSize   = inputSize mA
>       , outputSize  = outputSize mB
>       , regularized = (map L $ regularized mB) ++ (map R $ regularized mA)
>       , function    = \ p -> (function mB (termL p)) . (function mA (termR p))
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




foo :: (Num a) => [a] -> a
foo xs = sum $ map (\z -> z*z) xs

bar :: [Double] -> [Double]
bar = grad foo