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
> import IndexIsos
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
> -- three tensors, any size
> arbTensorTriple
>   :: (Arbitrary r)
>   => r -> Gen (Tensor r, Tensor r, Tensor r)
> arbTensorTriple _ = do
>   a <- arbitrary >>= arbTensor
>   b <- arbitrary >>= arbTensor
>   c <- arbitrary >>= arbTensor
>   return (a,b,c)
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


Index Tests
-----------

> _test_mapIndex_indexOf :: Size -> Size -> Bool
> _test_mapIndex_indexOf u v = and
>   [ (indexOf v) == fmap (mapIndex u v) (indexOf u)
>   , (indexOf u) == fmap (mapIndex v u) (indexOf v)
>   ]

> _test_mapIndex_indexOf_self :: Test (Size -> Bool)
> _test_mapIndex_indexOf_self =
>   testName "mapIndex self" $
>     \u -> _test_mapIndex_indexOf u u

> _test_mapIndex_indexOf_plus_zero :: Test (Size -> Bool)
> _test_mapIndex_indexOf_plus_zero =
>   testName "mapIndex plus zero" $
>     \u -> and
>       [ _test_mapIndex_indexOf u (u :+ 0)
>       , _test_mapIndex_indexOf u (0 :+ u)
>       ]

> _test_mapIndex_indexOf_times_zero :: Test (Size -> Bool)
> _test_mapIndex_indexOf_times_zero =
>   testName "mapIndex times zero" $
>     \u -> and
>       [ _test_mapIndex_indexOf 0 (u :* 0)
>       , _test_mapIndex_indexOf 0 (0 :* u)
>       ]

> _test_mapIndex_indexOf_times_one :: Test (Size -> Bool)
> _test_mapIndex_indexOf_times_one =
>   testName "mapIndex times one" $
>     \u -> and
>       [ _test_mapIndex_indexOf u (u :* 1)
>       , _test_mapIndex_indexOf u (1 :* u)
>       ]

> _test_mapIndex_indexOf_plus_comm :: Test (Size -> Size -> Bool)
> _test_mapIndex_indexOf_plus_comm =
>   testName "mapIndex plus_comm" $
>     \u v -> _test_mapIndex_indexOf (u :+ v) (v :+ u)

> _test_mapIndex_indexOf_plus_assoc :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_plus_assoc =
>   testName "mapIndex plus assoc" $
>     \u v w -> _test_mapIndex_indexOf ((u :+ v) :+ w) (u :+ (v :+ w))

> _test_mapIndex_indexOf_times_assoc
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_assoc =
>   testName "mapIndex times assoc" $
>     \u v w -> _test_mapIndex_indexOf ((u :* v) :* w) (u :* (v :* w))

> _test_mapIndex_indexOf_times_distR
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_distR =
>   testName "mapIndex times distR" $
>     \u v w -> _test_mapIndex_indexOf ((u :+ v) :* w) ((u :* w) :+ (v :* w))

> _test_mapIndex_indexOf_times_distL
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_distL =
>   testName "mapIndex times distL" $
>     \u v w -> _test_mapIndex_indexOf (u :* (v :+ w)) ((u :* v) :+ (u :* w))


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

We can extract the terms from an ``oplus``.

> _test_termL_oplus
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Tensor r -> Tensor r -> Bool)
> _test_termL_oplus r =
>   testName "a == termL (oplus a b)" $
>     \a b -> a == termL (a ⊕ b)
> 
> _test_termR_oplus
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Tensor r -> Tensor r -> Bool)
> _test_termR_oplus r =
>   testName "b == termR (oplus a b)" $
>     \a b -> b == termR (a ⊕ b)

> _test_oplus_assoc
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_assoc r =
>   testName "oplus is associative" $
>     \a b c -> ((a ⊕ b) ⊕ c) == (a ⊕ (b ⊕ c))

> _test_otimes_assoc
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_otimes_assoc r =
>   testName "otimes is associative" $
>     \a b c -> ((a ⊗ b) ⊗ c) == (a ⊗ (b ⊗ c))

> _test_oplus_otimes_distR
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_otimes_distR r =
>   testName "otimes right distributive" $
>     \a b c -> ((a ⊕ b) ⊗ c) == ((a ⊗ c) ⊕ (b ⊗ c))

> -- this requires an isomorphism I haven't found yet grr
> _test_oplus_otimes_distL
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_otimes_distL r =
>   testName "otimes left distributive" $
>     \a b c -> (a ⊗ (b ⊕ c)) == ((a ⊗ b) ⊕ (a ⊗ c))

The ``comm`` operator is an involution on both sum and product type tensors.

> _test_comm_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_comm_sum r =
>   testName "(:+) comm . comm $== id" $
>     forAllShrink (arbTensorSum r) shrink $
>     \m -> comm (comm m) $== m
> 
> _test_comm_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_comm_prod r =
>   testName "(:*) comm . comm $== id" $
>     forAllShrink (arbTensorProd r) shrink $
>     \m -> comm (comm m) $== m

The ``assocL`` and ``assocR`` operators are mutual inverses on both sum and product tensors of the appropriate shape.

> _test_assocL_assocR_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocL_assocR_sum r =
>   testName "(:+) assocL . assocR $== id" $
>     forAllShrink (arbTripleSumL r) shrink $
>     \m -> assocL (assocR m) $== m
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
>   testName "(:+) assocR . assocL $== id" $
>     forAllShrink (arbTripleSumR r) shrink $
>     \m -> assocR (assocL m) $== m
>   where
>     arbTripleSumR :: (Arbitrary r)
>       => r -> Gen (Tensor r)
>     arbTripleSumR _ = do
>       (u,v,w) <- arbitrary
>       arbTensor (u :+ (v :+ w))
> 
> _test_assocL_assocR_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test Property
> _test_assocL_assocR_prod r =
>   testName "(:*) assocL . assocR $== id" $
>     forAll (arbTripleProdL r) $
>     \m -> assocL (assocR m) $== m
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
>   testName "(:*) assocR . assocL $== id" $
>     forAll (arbTripleProdR r) $
>     \m -> assocR (assocL m) $== m
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
>   -- mapIndex
>   runTest args _test_mapIndex_indexOf_self
>   runTest args _test_mapIndex_indexOf_plus_zero
>   runTest args _test_mapIndex_indexOf_times_zero
>   runTest args _test_mapIndex_indexOf_times_one
>   runTest args _test_mapIndex_indexOf_plus_comm
>   runTest args _test_mapIndex_indexOf_plus_assoc
>   runTest args _test_mapIndex_indexOf_times_assoc
>   runTest args _test_mapIndex_indexOf_times_distR
>   runTest args _test_mapIndex_indexOf_times_distL
> 
>   -- vector
>   runTest args (_test_same_size_op_comm "(.+)" r (.+))
>   runTest args (_test_same_size_op_comm "(.*)" r (.*))
> 
>   -- structure
>   runTest args (_test_termL_oplus r)
>   runTest args (_test_termR_oplus r)
>   runTest args (_test_oplus_assoc r)
>   runTest args (_test_otimes_assoc r)
>   runTest args (_test_oplus_otimes_distR r)
>   skipTest args (_test_oplus_otimes_distL r)
>   runTest args (_test_comm_sum r)
>   runTest args (_test_comm_prod r)
>   runTest args (_test_assocL_assocR_sum r)
>   runTest args (_test_assocR_assocL_sum r)
>   runTest args (_test_assocL_assocR_prod r)
>   runTest args (_test_assocR_assocL_prod r)
> 
> main_tensor :: IO ()
> main_tensor = do
>   _test_tensor (0::Int) 100 3
