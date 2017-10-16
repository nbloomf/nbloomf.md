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


Test Case Generators
--------------------

A lot of these tests will need ad-hoc generators to be useful. For example, tensor addition is (should be) commutative; that is, we should have $$a + b = b + a$$ whenever the sum makes sense. And that qualification is the rub: for the vast majority of $a$ and $b$, $a + b$ does not make sense. We can only add tensors that have the same size, and the test case generator for this property will need to take that into account. The following generator can do this.

> arbTensorPairSameSize :: (Arbitrary r) => r -> Gen (Tensor r, Tensor r)
> arbTensorPairSameSize _ = do
>   u <- arbitrary
>   a <- arbTensor u
>   b <- arbTensor u
>   return (a,b)

Now it so happens that this generator will be useful for testing a few different identities, so it makes sense to define it as a separate function. But there are other identities that will need more or less unique generators. For these, we'll use a ``where`` clause to avoid polluting the namespace. But the more generalizable generators will go here.

> -- two tensors, any size
> arbTensorPair
>   :: (Arbitrary r)
>   => r -> Gen (Tensor r, Tensor r)
> arbTensorPair _ = do
>   a <- arbitrary >>= arbTensor
>   b <- arbitrary >>= arbTensor
>   return (a,b)
> 
> -- having shape (* :+ *))
> arbTensorSum
>   :: (Arbitrary r)
>   => r -> Gen (Tensor r)
> arbTensorSum _ = do
>   (u,v) <- arbitrary
>   arbTensor (u :+ v)
> 
> -- having shape (* :* *)
> arbTensorProd
>   :: (Arbitrary r)
>   => r -> Gen (Tensor r)
> arbTensorProd _ = do
>   (u,v) <- arbitrary
>   arbTensor (u :* v)


Vector Arithmetic Tests
-----------------------

We have a few operations with signature $\mathbb{R}^s \rightarrow \mathbb{R}^s \rightarrow \mathbb{R}^t$ that are commutative; notably, tensor addition and pointwise multiplication. ``_test_same_size_op_comm`` can test these.

> _test_same_size_op_comm
>   :: (Eq r, Num r, Show r, Arbitrary r)
>   => String -> r -> (Tensor r -> Tensor r -> Tensor r) -> Test Property
> _test_same_size_op_comm s r op =
>   testName (s ++ " (op a b) == (op b a)") $
>     forAll (arbTensorPairSameSize r) $
>     \(a,b) -> (op a b) == (op b a)


Structural Arithmetic Tests
---------------------------

> _test_termL_oplus
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_termL_oplus r =
>   testName "a == termL (oplus a b)" $
>     forAll (arbTensorPair r) $
>     \(a,b) -> a == termL (oplus a b)
> 
> _test_termR_oplus
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_termR_oplus r =
>   testName "b == termR (oplus a b)" $
>     forAll (arbTensorPair r) $
>     \(a,b) -> b == termR (oplus a b)

> _test_comm_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_comm_sum r =
>   testName "(:+) comm . comm == id" $
>     forAll (arbTensorSum r) $
>     \m -> comm (comm m) == m
> 
> _test_comm_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_comm_prod r =
>   testName "(:*) comm . comm == id" $
>     forAll (arbTensorProd r) $
>     \m -> comm (comm m) == m

> _test_assocL_assocR_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocL_assocR_sum r =
>   testName "(:+) assocL . assocR == id" $
>     forAll (arbTripleSumL r) $
>     \m -> assocL (assocR m) == m
>   where
>     arbTripleSumL :: (Arbitrary r)
>       => r -> Gen (Tensor r)
>     arbTripleSumL _ = do
>       (u,v,w) <- arbitrary
>       arbTensor ((u :+ v) :+ w)
> 
> _test_assocR_assocL_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocR_assocL_sum r =
>   testName "(:+) assocR . assocL == id" $
>     forAll (arbTripleSumR r) $
>     \m -> assocR (assocL m) == m
>   where
>     arbTripleSumR :: (Arbitrary r)
>       => r -> Gen (Tensor r)
>     arbTripleSumR _ = do
>       (u,v,w) <- arbitrary
>       arbTensor (u :+ (v :+ w))

> _test_assocL_assocR_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocL_assocR_prod r =
>   testName "(:*) assocL . assocR == id" $
>     forAll (arbTripleProdL r) $
>     \m -> assocL (assocR m) == m
>   where
>     arbTripleProdL :: (Arbitrary r)
>       => r -> Gen (Tensor r)
>     arbTripleProdL _ = do
>       (u,v,w) <- arbitrary
>       arbTensor ((u :* v) :* w)
> 
> _test_assocR_assocL_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocR_assocL_prod r =
>   testName "(:*) assocR . assocL == id" $
>     forAll (arbTripleProdR r) $
>     \m -> assocR (assocL m) == m
>   where
>     arbTripleProdR :: (Arbitrary r)
>       => r -> Gen (Tensor r)
>     arbTripleProdR _ = do
>       (u,v,w) <- arbitrary
>       arbTensor (u :* (v :* w))


The Test Suite
--------------

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
>   runTest args (_test_termL_oplus r)
>   runTest args (_test_termR_oplus r)
>   runTest args (_test_same_size_op_comm "(.+)" r (.+))
>   runTest args (_test_same_size_op_comm "(.*)" r (.*))
>   runTest args (_test_comm_sum r)
>   runTest args (_test_comm_prod r)
>   runTest args (_test_assocL_assocR_sum r)
>   runTest args (_test_assocR_assocL_sum r)
>   runTest args (_test_assocL_assocR_prod r)
>   runTest args (_test_assocR_assocL_prod r)
> 
> main_tensor :: IO ()
> main_tensor = do
>   _test_tensor (0::Int) 200 10
>   _test_tensor (0::Double) 200 10
