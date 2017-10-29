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


Index Tests
-----------

> _test_mapIndex_indexOf
>   :: Size -> Size -> Bool
> _test_mapIndex_indexOf u v = and
>   [ (indexOf v) == fmap (mapIndex u v) (indexOf u)
>   , (indexOf u) == fmap (mapIndex v u) (indexOf v)
>   ]
> 
> _test_mapIndex_indexOf_self
>   :: Test (Size -> Bool)
> _test_mapIndex_indexOf_self =
>   testName "mapIndex self" $
>     \u -> _test_mapIndex_indexOf u u
> 
> _test_mapIndex_indexOf_plus_zero
>   :: Test (Size -> Bool)
> _test_mapIndex_indexOf_plus_zero =
>   testName "mapIndex plus zero" $
>     \u -> and
>       [ _test_mapIndex_indexOf u (u :+ 0)
>       , _test_mapIndex_indexOf u (0 :+ u)
>       ]
> 
> _test_mapIndex_indexOf_times_zero
>   :: Test (Size -> Bool)
> _test_mapIndex_indexOf_times_zero =
>   testName "mapIndex times zero" $
>     \u -> and
>       [ _test_mapIndex_indexOf 0 (u :* 0)
>       , _test_mapIndex_indexOf 0 (0 :* u)
>       ]
> 
> _test_mapIndex_indexOf_times_one
>   :: Test (Size -> Bool)
> _test_mapIndex_indexOf_times_one =
>   testName "mapIndex times one" $
>     \u -> and
>       [ _test_mapIndex_indexOf u (u :* 1)
>       , _test_mapIndex_indexOf u (1 :* u)
>       ]
> 
> _test_mapIndex_indexOf_plus_comm
>   :: Test (Size -> Size -> Bool)
> _test_mapIndex_indexOf_plus_comm =
>   testName "mapIndex plus_comm" $
>     \u v -> _test_mapIndex_indexOf (u :+ v) (v :+ u)
> 
> _test_mapIndex_indexOf_plus_assoc
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_plus_assoc =
>   testName "mapIndex plus assoc" $
>     \u v w -> _test_mapIndex_indexOf
>       ((u :+ v) :+ w) (u :+ (v :+ w))
> 
> _test_mapIndex_indexOf_times_assoc
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_assoc =
>   testName "mapIndex times assoc" $
>     \u v w -> _test_mapIndex_indexOf
>       ((u :* v) :* w) (u :* (v :* w))
> 
> _test_mapIndex_indexOf_times_distR
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_distR =
>   testName "mapIndex times distR" $
>     \u v w -> _test_mapIndex_indexOf
>       ((u :+ v) :* w) ((u :* w) :+ (v :* w))
> 
> _test_mapIndex_indexOf_times_distL
>   :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_indexOf_times_distL =
>   testName "mapIndex times distL" $
>     \u v w -> _test_mapIndex_indexOf
>       (u :* (v :+ w)) ((u :* v) :+ (u :* w))


Vector Arithmetic Tests
-----------------------

We have a few operations with signature $\mathbb{R}^s \rightarrow \mathbb{R}^s \rightarrow \mathbb{R}^t$ that are commutative; notably, tensor addition and pointwise multiplication. ``_test_same_size_op_comm`` can test these.

> _test_same_size_op_comm
>   :: (Eq r, Num r, Show r, Arbitrary r)
>   => String -> r -> (Tensor r -> Tensor r -> Tensor r)
>   -> Test (Size -> Property)
> _test_same_size_op_comm s r op =
>   testName (s ++ " (op a b) == (op b a)") $
>     \u ->
>       forAll2 (arbTensorOf r u) (arbTensorOf r u) $
>         \a b -> (op a b) == (op b a)


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

``oplus`` and ``otimes`` are associative.

> _test_oplus_assoc
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_assoc r =
>   testName "oplus is associative" $
>     \a b c -> ((a ⊕ b) ⊕ c) == (a ⊕ (b ⊕ c))
> 
> _test_otimes_assoc
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_otimes_assoc r =
>   testName "otimes is associative" $
>     \a b c -> ((a ⊗ b) ⊗ c) == (a ⊗ (b ⊗ c))

``otimes`` distributes over ``oplus`` from the right. From the left, it's... more complicated.

> _test_oplus_otimes_distR
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_otimes_distR r =
>   testName "otimes right distributive" $
>     \a b c -> ((a ⊕ b) ⊗ c) == ((a ⊗ c) ⊕ (b ⊗ c))
> 
> -- this requires an extra isomorphism I haven't found yet grr
> _test_oplus_otimes_distL
>   :: (Eq r, Show r, Arbitrary r, Num r)
>   => r -> Test (Tensor r -> Tensor r -> Tensor r -> Bool)
> _test_oplus_otimes_distL r =
>   testName "otimes left distributive" $
>     \a b c -> (a ⊗ (b ⊕ c)) == ((a ⊗ b) ⊕ (a ⊗ c))

The ``comm`` operator is an involution on both sum and product type tensors.

> _test_comm_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_comm_sum r =
>   testName "(:+) comm . comm $== id" $
>     \u v ->
>       forAll (arbTensorOf r (u :+ v)) $
>         \m -> comm (comm m) $== m
> 
> _test_comm_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_comm_prod r =
>   testName "(:*) comm . comm $== id" $
>     \u v ->
>       forAll (arbTensorOf r (u :* v)) $
>         \m -> comm (comm m) $== m

The ``assocL`` and ``assocR`` operators are mutual inverses on both sum and product tensors of the appropriate shape.

> _test_assocL_assocR_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Property)
> _test_assocL_assocR_sum r =
>   testName "(:+) assocL . assocR $== id" $
>     \u v w ->
>       forAll (arbTensorOf r ((u :+ v) :+ w)) $
>         \m -> assocL (assocR m) $== m
> 
> _test_assocR_assocL_sum
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Property)
> _test_assocR_assocL_sum r =
>   testName "(:+) assocR . assocL $== id" $
>     \u v w ->
>       forAll (arbTensorOf r (u :+ (v :+ w))) $
>         \m -> assocR (assocL m) $== m
> 
> _test_assocL_assocR_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Property)
> _test_assocL_assocR_prod r =
>   testName "(:*) assocL . assocR $== id" $
>     \u v w ->
>       forAll (arbTensorOf r ((u :* v) :* w)) $
>         \m -> assocL (assocR m) $== m
> 
> _test_assocR_assocL_prod
>   :: (Eq r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Property)
> _test_assocR_assocL_prod r =
>   testName "(:*) assocR . assocL $== id" $
>     \u v w ->
>       forAll (arbTensorOf r (u :* (v :* w))) $
>         \m -> assocR (assocL m) $== m
> 
> _test_vcat_is_oplus
>  :: (Eq r, Show r, Arbitrary r)
>  => r -> Test (Size -> Size -> Size -> Property)
> _test_vcat_is_oplus r =
>   testName "vcat is oplus" $
>     \u v w ->
>       forAll2 (arbTensorOf r (u :* w)) (arbTensorOf r (v :* w)) $
>         \a b -> (a ~-~ b) == (oplus a b)
> 
> -- pretty sure this depends on the iso from left distributivity
> _test_hcat_is_oplus
>  :: (Eq r, Show r, Arbitrary r)
>  => r -> Test (Size -> Size -> Size -> Property)
> _test_hcat_is_oplus r =
>   testName "hcat is oplus" $
>     \u v w ->
>       forAll2 (arbTensorOf r (u :* w)) (arbTensorOf r (v :* w)) $
>         \a b -> (a ~|~ b) == (oplus a b)


Matrix Tests
------------

> _test_matmul_id
>   :: (Eq r, Num r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_matmul_id r =
>   testName "idMat is (***) neutral" $
>     \u v ->
>       forAll (arbTensorOf r (u :* v)) $
>         \m -> and
>           [ m == (m *** (idMat v))
>           , m == ((idMat u) *** m)
>           ]
> 
> _test_matmul_assoc
>   :: (Eq r, Num r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Size -> Property)
> _test_matmul_assoc r =
>   testName "(***) is associative" $
>   \u v w x ->
>     forAll3
>       (arbTensorOf r (u :* v))
>       (arbTensorOf r (v :* w))
>       (arbTensorOf r (w :* x)) $
>       \a b c -> (a *** (b *** c)) == ((a *** b) *** c)


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
>   runTest args (_test_vcat_is_oplus r)
>   skipTest args (_test_hcat_is_oplus r)
> 
>   runTest args (_test_matmul_id r)
>   runTest args (_test_matmul_assoc r)
> 
> main_tensor :: IO ()
> main_tensor = do
>   _test_tensor (0::Int) 100 3
