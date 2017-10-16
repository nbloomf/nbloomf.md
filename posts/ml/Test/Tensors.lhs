---
title: Tensor Tests
author: nbloomf
date: 2017-10-14
tags: ml, literate-haskell
---

First some boilerplate.

> module Test.Tensors where
> 
> import Data.Array
> import Text.PrettyPrint
> import Test.QuickCheck
> 
> import Indices
> import Tensors

In the last post we defined a ``Tensor`` data type and a bunch of operations on it. Our tensor operations satisfy a bunch of identities that we can turn into executable tests. I've put them here to avoid cluttering up the main code too much.

> arbTensorSum :: (Arbitrary r) => r -> Gen (Tensor r)
> arbTensorSum _ = do
>   (u,v) <- arbitrary
>   arbTensor (u :+ v)

> arbTensorProd :: (Arbitrary r) => r -> Gen (Tensor r)
> arbTensorProd _ = do
>   (u,v) <- arbitrary
>   arbTensor (u :* v)

> arbTensorPairSameSize :: (Arbitrary r) => r -> Gen (Tensor r, Tensor r)
> arbTensorPairSameSize _ = do
>   u <- arbitrary
>   a <- arbTensor u
>   b <- arbTensor u
>   return (a,b)

> _test_same_size_op_comm
>   :: (Eq r, Num r, Show r, Arbitrary r)
>   => r -> (Tensor r -> Tensor r -> Tensor r) -> Test Property
> _test_same_size_op_comm r op =
>   testName "_test_same_size_op_comm" $
>     forAll (arbTensorPairSameSize r) $
>     \(a,b) -> (op a b) == (op b a)

> _test_comm_sum
>   :: (Eq r, Show r, Arbitrary r) => r -> Test Property
> _test_comm_sum r =
>   testName "_test_comm_sum" $
>     forAll (arbTensorSum r) $
>     \m -> m == comm (comm m)

> _test_comm_prod
>   :: (Eq r, Show r, Arbitrary r) => r -> Test Property
> _test_comm_prod r =
>   testName "_test_comm_prod" $
>     forAll (arbTensorProd r) $
>     \m -> m == comm (comm m)

> _test_assocL_assocR_sum
>   :: (Eq r, Show r, Arbitrary r) => r -> Test Property
> _test_assocL_assocR_sum r =
>   testName "_test_assocL_assocR_sum" $
>     forAll (arbTripleSumL r) $
>     \m -> m == assocL (assocR m)
>   where
>     arbTripleSumL :: (Arbitrary r) => r -> Gen (Tensor r)
>     arbTripleSumL _ = do
>       (u,v,w) <- arbitrary
>       arbTensor ((u :+ v) :+ w)

> _test_assocR_assocL_sum
>   :: (Eq r, Show r, Arbitrary r) => r -> Test Property
> _test_assocR_assocL_sum r =
>   testName "_test_assocR_assocL_sum" $
>     forAll (arbTripleSumR r) $
>     \m -> m == assocR (assocL m)
>   where
>     arbTripleSumR :: (Arbitrary r) => r -> Gen (Tensor r)
>     arbTripleSumR _ = do
>       (u,v,w) <- arbitrary
>       arbTensor (u :+ (v :+ w))

> -- test suite for Tensor
> _test_tensor
>   :: (Num r, Eq r, Show r, Arbitrary r, TypeName r)
>   => r -> Int -> Int -> IO ()
> _test_tensor r num size = do
>   testLabel ("Tensor " ++ typeName r)
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_same_size_op_comm r (.+))
>   runTest args (_test_same_size_op_comm r (.*))
>   runTest args (_test_comm_sum r)
>   runTest args (_test_comm_prod r)
>   runTest args (_test_assocL_assocR_sum r)
>   runTest args (_test_assocR_assocL_sum r)
> 
> main_tensor :: IO ()
> main_tensor = do
>   _test_tensor (0::Int) 200 10
>   _test_tensor (0::Double) 200 10
