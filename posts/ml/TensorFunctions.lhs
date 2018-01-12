---
title: Tensor Functions
author: nbloomf
date: 2017-10-16
tags: ml, literate-haskell
---

First some boilerplate.

> module TensorFunctions where
> 
> import Control.Applicative
> import Test.QuickCheck hiding (Function)
> import Test.QuickCheck.Test
> import Debug.Trace
> 
> import Indices
> import IndexIsos
> import Tensors

Ostensibly a "tensor function" is just a function with signature ``Tensor r -> Tensor r``. But it turns out this is not quite right. Tensor functions should be well defined on size -- a function should expect as input functions of some uniform size $u$ and should produce tensors of some other uniform size $v$. As we've implemented tensors here, plain haskell functions can't enforce this, so we'll abstract functions behind a type that can.

> data Function r = F
>   { dom :: Size -- domain (input) size
>   , cod :: Size -- codomain (output) size
>   , fun :: Tensor r -> Tensor r
>   }
> 
> -- apply
> ($@) :: Function r -> Tensor r -> Tensor r
> f $@ v = if (size v) /= dom f
>   then error $ "($@): domain mismatch: got " ++ show (size v)
>     ++ " but expected " ++ show (dom f)
>   else let w = (fun f) v in
>     if (size w) == cod f
>       then w
>       else error $ "($@): codomain mismatch: got " ++ show (size w)
>         ++ " but expected " ++ show (cod f)
> 
> -- compose
> ($.) :: Function r -> Function r -> Function r
> g $. f =
>   if (dom g) == (cod f)
>     then F
>       { dom = dom f
>       , cod = cod g
>       , fun = \v -> g $@ (f $@ v)
>       }
>     else
>       error "($.): domain/codomain mismatch"
> 
> infixr 0 $@
> infixr 9 $.

We can also build a small library of functions in this style.

> -- constant function
> constF :: (Num r) => Size -> Tensor r -> Function r
> constF u a = F
>   { dom = u
>   , cod = size a
>   , fun = \_ -> a
>   }
> 
> -- identity function
> idF :: Size -> Function r
> idF u = F
>   { dom = u
>   , cod = u
>   , fun = id
>   }
> 
> -- scalar multiplication
> scalarF :: (Num r) => Size -> r -> Function r
> scalarF u k = F
>   { dom = u
>   , cod = u
>   , fun = \v -> k .@ v
>   }
> 
> -- matrix-vector multiplication
> linearF :: (Num r) => Tensor r -> Function r
> linearF m@(T (v :* u) _) = F
>   { dom = u
>   , cod = v
>   , fun = \w -> m **> w
>   }
> linearF _ = error "linearF: parameter should have product shape."
> 
> -- matrix-vector multiplication plus a constant
> affineF :: (Num r) => Tensor r -> Tensor r -> Function r
> affineF m@(T (v :* u) _) b@(T w _) =
>   if v == w
>     then F
>       { dom = u
>       , cod = v
>       , fun = \z -> (m **> z) .+ b
>       }
>     else error "affineF: dimension mismatch"
> affineF _ _ = error "affineF: first parameter should have product shape."
> 
> -- pointwise eval
> pointwiseF :: (Num r) => Size -> (r -> r) -> Function r
> pointwiseF u f = F
>   { dom = u
>   , cod = u
>   , fun = \v -> fmap f v
>   }
> 
> -- diagonalize
> diagF :: (Num r) => Size -> Function r
> diagF u = F
>   { dom = u
>   , cod = u :* u
>   , fun = diag
>   }
> 
> cellF :: Size -> (Tensor r -> r) -> Function r
> cellF u f = F
>   { dom = u
>   , cod = 1
>   , fun = \v -> cell $ f v
>   }

And direct summing:

> dSumR :: Size -> Tensor r -> Function r
> dSumR u a@(T v _) = F
>   { dom = u
>   , cod = u :+ v
>   , fun = \x -> x `oplus` a
>   }
> 
> dSumL :: Size -> Tensor r -> Function r
> dSumL u a@(T v _) = F
>   { dom = u
>   , cod = v :+ u
>   , fun = \x -> a `oplus` x
>   }


Algebra of Functions
--------------------

For fun we can describe an algebra of tensor functions. There's sums:

> instance Vector Function where
>   r .@ f = F
>     { dom = dom f
>     , cod = cod f
>     , fun = \v -> r .@ (f $@ v)
>     }
> 
>   f .+ g
>     | (dom f) /= (dom g) = error "Function (.+): domains must match"
>     | (cod f) /= (cod g) = error "Function (.+): codomains must match"
>     | otherwise = F
>         { dom = dom f
>         , cod = cod f
>         , fun = \v -> (f $@ v) .+ (g $@ v)
>         }
> 
>   neg f = F
>     { dom = dom f
>     , cod = cod f
>     , fun = \v -> neg (f $@ v)
>     }

> (+++) :: Function r -> Function r -> Function r
> f +++ g = F
>   { dom = (dom f) :+ (dom g)
>   , cod = (cod f) :+ (cod g)
>   , fun = \v -> (f $@ termL v) `oplus` (g $@ termR v)
>   }

And mapping into products.

> mapR :: Size -> Function r -> Function r
> mapR u f = F
>   { dom = u :* (dom f)
>   , cod = u :* (cod f)
>   , fun = \a -> tensor (u :* (cod f)) $
>       \(i :& j) -> (f $@ projR i a) `at'` j
>   }
> 
> mapL :: Size -> Function r -> Function r
> mapL u f = F
>   { dom = (dom f) :* u
>   , cod = (cod f) :* u
>   , fun = \a -> tensor ((cod f) :* u) $
>       \(i :& j) -> (f $@ projL j a) `at'` i
>   }

As an example, given a matrix we can use the ``map*`` operators to sum or maximum of the rows or columns of a product-shaped tensor.

> rowsBy :: (Tensor r -> r) -> Tensor r -> Tensor r
> rowsBy f a@(T (u :* v) _) =
>   mapR u (cellF v f) $@ a
> 
> colsBy :: (Tensor r -> r) -> Tensor r -> Tensor r
> colsBy f a@(T (u :* v) _) =
>   mapL v (cellF u f) $@ a
