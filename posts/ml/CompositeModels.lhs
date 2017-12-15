---
title: Composite Models
author: nbloomf
date: 2017-10-22
tags: ml, literate-haskell
---

Boilerplate.

> {-# LANGUAGE LambdaCase #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module CompositeModels where
> 
> import Control.Applicative
> import Test.QuickCheck
> import Test.QuickCheck.Test
> 
> import Indices
> import IndexIsos
> import Tensors
> import TensorFunctions
> import Gradients
> import GradientChecking
> import GradientDescent
> import SupervisedModels

In the last post we defined *supervised model* and gave the basic example of an affine model. In order to learn more interesting functions, we need more complex kinds of models.  Rather than defining more and more complicated models by hand, we'd like to describe them *compositionally*, by taking a small number of "atomic" models (like the affine example) and plugging them together in a small number of different ways. In this post we'll compose two models by taking the output of one as the input of another -- this will be function composition with a twist.

First, suppose we have two mappings $$f : \mathbb{R}^{\Theta \oplus A} \rightarrow \mathbb{R}^B$$ and $$g : \mathbb{R}^{\Phi \oplus B} \rightarrow \mathbb{R}^C.$$ We'd like to compose these together, making a single function with parameter $\Phi \oplus \Theta$. We'll do this by introducing an operator on functions. Define $$g \bullet f : \mathbb{R}^{(\Phi \oplus \Theta) \oplus A} \rightarrow \mathbb{R}^C$$ by $$(g \bullet f)((M \oplus N) \oplus V) = g(M \oplus f(N \oplus V)).$$ This is function composition with a parameter, and the gradient has signature $$\nabla(g \bullet f) : \mathbb{R}^{(\Phi \oplus \Theta) \oplus A} \rightarrow \mathbb{R}^{C \otimes ((\Phi \oplus \Theta) \oplus A)}.$$ We can compute $\nabla(g \bullet f)$ by case analysis on the index; each one has one of the following forms:

1. $c \& \mathsf{L}\mathsf{L}\phi$ with $c \in C$ and $\phi \in \Phi$,
2. $c \& \mathsf{L}\mathsf{R}\theta$ with $c \in C$ and $\theta \in \Theta$,
3. $c \& \mathsf{R}a$ with $c \in C$ and $a \in A$.

At $c \& \mathsf{L}\mathsf{L}\phi$, we have

$$\begin{eqnarray*}
 &   & \nabla(g \bullet f)((M \oplus N) \oplus V)_{c \& \mathsf{L}\mathsf{L}\phi} \\
 & = & D((g \bullet f)(w_{\mathsf{L}\mathsf{L}\phi,(M \oplus N) \oplus V}(x))_c)(((M \oplus N) \oplus V)_{\mathsf{L}\mathsf{L}\phi}) \\
 & = & D((g \bullet f)((w_{\phi,M}(x) \oplus N) \oplus V)_c)(M_\phi) \\
 & = & D(g(w_{\phi,M}(x) \oplus f(N \oplus V))_c)(M_\phi) \\
 & = & D((g \circ (- \oplus f(N \oplus V)))(w_{\phi,M}(x))_c)(M_\phi) \\
 & = & \nabla(g \circ (- \oplus f(N \oplus V)))(M)_{c \& \phi} \\
 & = & \left( \nabla(g)((- \oplus f(N \oplus V))(M)) \cdot \nabla(- \oplus f(N \oplus V))(M) \right)_{c \& \phi} \\
 & = & \left( \nabla(g)(M \oplus f(N \oplus V)) \cdot \nabla(- \oplus f(N \oplus V))(M) \right)_{c \& \phi} \\
 & = & \left( \nabla(g)(M \oplus f(N \oplus V)) \cdot \mathsf{vcat}(\mathsf{Id}_{\Phi}, \mathsf{Z}_{B \otimes \Phi}) \right)_{c \& \phi}
\end{eqnarray*}$$

At $c \& \mathsf{L}\mathsf{R}\theta$, we have

$$\begin{eqnarray*}
 &   & \nabla(g \bullet f)((M \oplus N) \oplus V)_{c \& \mathsf{L}\mathsf{R}\theta} \\
 & = & D((g \bullet f)(w_{\mathsf{L}\mathsf{R}\theta,(M \oplus N) \oplus V}(x))_c)(((M \oplus N) \oplus V)_{\mathsf{L}\mathsf{R}\theta}) \\
 & = & D((g \bullet f)((M \oplus w_{\theta,N}(x)) \oplus V)_c)(N_\theta) \\
 & = & D(g(M \oplus f(w_{\theta,N}(x) \oplus V))_c)(N_\theta) \\
 & = & D((g(M \oplus -) \circ f(- \oplus V))(w_{\theta,N}(x))_c)(N_\theta) \\
 & = & \nabla(g(M \oplus -) \circ f(- \oplus V))(N)_{c \& \theta} \\
 & = & \left( \nabla(g(M \oplus -))(f(- \oplus V)(N)) \cdot \nabla(f(- \oplus V))(N) \right)_{c \& \theta} \\
 & = & \left( \nabla(g \circ (M \oplus -))(f(N \oplus V)) \cdot \nabla(f \circ (- \oplus V))(N) \right)_{c \& \theta} \\
 & = & \left( (\nabla g)((M \oplus -)(f(N \oplus V))) \cdot \nabla(M \oplus -)(f(N \oplus V)) \cdot (\nabla f)((- \oplus V)(N)) \cdot \nabla(- \oplus V)(N) \right)_{c \& \theta} \\
 & = & \left( \underbrace{(\nabla g)(M \oplus f(N \oplus V))}_{C \otimes (\Phi \oplus B)} \cdot \underbrace{\mathsf{vcat}(\mathsf{Z}_{\Phi \otimes B}, \mathsf{Id}_{B})}_{(\Phi \oplus B) \otimes B} \cdot \underbrace{(\nabla f)(N \oplus V)}_{B \otimes (\Theta \oplus A)} \cdot \underbrace{\mathsf{vcat}(\mathsf{Id}_{\Theta}, \mathsf{Z}_{A \otimes \Theta})}_{(\Theta \oplus A) \otimes \Theta} \right)_{c \& \theta} \\
\end{eqnarray*}$$

(I've included the size of each factor as a smell test.)

At $c \& \mathsf{R}a$, we have

$$\begin{eqnarray*}
 &   & \nabla(g \bullet f)((M \oplus N) \oplus V)_{c \& \mathsf{R}a} \\
 & = & D((g \bullet f)(w_{\mathsf{R}a, (M \oplus N) \oplus V}(x))_c)(((M \oplus N) \oplus V)_{\mathsf{R}a}) \\
 & = & D((g \bullet f)((M \oplus N) \oplus w_{a,v}(x))_c)(V_a) \\
 & = & D(g(M \oplus f(N \oplus w_{a,V}(x)))_c)(V_a) \\
 & = & D((g(M \oplus -) \circ f(N \oplus -))(w_{a,V}(x))_c)(V_a) \\
 & = & \nabla(g(M \oplus -) \circ f(N \oplus -))(V)_{c \& a} \\
 & = & \left( \nabla(g(M \oplus -))(f(N \oplus -)(V)) \cdot \nabla(f(N \oplus -))(V) \right)_{c \& a} \\
 & = & \left( \nabla(g \circ (M \oplus -))(f(N \oplus V)) \cdot \nabla(f \circ (N \oplus -))(V) \right)_{c \& a} \\
 & = & \left( (\nabla g)(M \oplus f(N \oplus V)) \cdot \nabla(M \oplus -)(f(N \oplus V)) \cdot (\nabla f)(N \oplus V) \cdot \nabla(N \oplus -)(V) \right)_{c \& a} \\
 & = & \left( \underbrace{(\nabla g)(M \oplus f(N \oplus V))}_{C \otimes (\Phi \oplus B)} \cdot \underbrace{\mathsf{vcat}(\mathsf{Z}_{\Phi \otimes B}, \mathsf{Id}_B)}_{(\Phi \oplus B) \otimes B} \cdot \underbrace{(\nabla f)(N \oplus V)}_{B \otimes (\Theta \oplus A)} \cdot \underbrace{\mathsf{vcat}(\mathsf{Z}_{\Theta \otimes A},\mathsf{Id}_{A})}_{(\Theta \oplus A) \otimes A} \right)_{c \& a} \\
\end{eqnarray*}$$

With this gradient in hand, we can compose two models together like so.

> (>>>)
>   :: (Num r)
>   => SupervisedModel r -> SupervisedModel r -> SupervisedModel r
> f >>> g =
>   let
>     theta = smParamSize f
>     a = smInputSize f
>     b = smOutputSize f
>     phi = smParamSize g
>     b' = smInputSize g
>     c = smOutputSize g
> 
>     fFun = smFunction f
>     fGrad = smGradient f
>     gFun = smFunction g
>     gGrad = smGradient g
>   in
>     if b' == b
>       then SM
>         { smParamSize = phi :+ theta
>         , smInputSize = a
>         , smOutputSize = c
>         , smRegularize =
>             (map L $ smRegularize f) ++ (map R $ smRegularize g)
> 
>         , smFunction = F
>             { dom = (phi :+ theta) :+ a
>             , cod = c
>             , fun = \x ->
>                 let
>                   m = termL $ termL x
>                   n = termR $ termL x
>                   v = termR x
>                 in
>                   gFun $@ (m ⊕ (fFun $@ (n ⊕ v)))
>             }
> 
>         , smGradient = F
>             { dom = (phi :+ theta) :+ a
>             , cod = c :* ((phi :+ theta) :+ a)
>             , fun = \x ->
>                 let
>                   m = termL $ termL x
>                   n = termR $ termL x
>                   v = termR x
>                 in
>                   tensor (c :* ((phi :+ theta) :+ a)) $ \case
>                     k :& (L (L p)) ->
>                       let
>                         mH = gGrad $@ (m ⊕ (fFun $@ (n ⊕ v)))
>                         mK = (idMat phi) `vcat` (zeros $ b :* phi)
>                       in
>                         (mH *** mK) `at` (k :& p)
>                     k :& (L (R t)) ->
>                       let
>                         mH = gGrad $@ (m ⊕ (fFun $@ (n ⊕ v)))
>                         mK = (zeros $ phi :* b) `vcat` (idMat b)
>                         mL = fGrad $@ (n ⊕ v)
>                         mM = (idMat theta) `vcat` (zeros $ a :* theta)
>                       in
>                         (mH *** mK *** mL *** mM) `at` (k :& t)
>                     k :& (R i) ->
>                       let
>                         mH = gGrad $@ (m ⊕ (fFun $@ (n ⊕ v)))
>                         mK = (zeros $ phi :* b) `vcat` (idMat b)
>                         mL = fGrad $@ (n ⊕ v)
>                         mM = (zeros $ theta :* a) `vcat` (idMat a)
>                       in
>                         (mH *** mK *** mL *** mM) `at` (k :& i)
>             }
>         }
>       else error "(>>>): inner dimensions must match"

And we can test the gradient of the composite of two affine models.

> _test_compose_affine_model_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r,
>       Floating r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Size -> Property)
> _test_compose_affine_model_dual_gradient r =
>   testName "compose affine model dual gradient check" $
>   \u v w -> (u ~/= 0) && (v ~/= 0) && (w ~/= 0) ==>
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (dualGrad $ smFunction $
>         ((affineSMOf (toDual r) u v)) >>> (affineSMOf (toDual r) v w))
>       (smGradient $ (affineSMOf r u v) >>> (affineSMOf r v w))

At this point we can describe affine models of arbitrary size, and compose models together. But the composite of two affine models is again affine. To introduce some nonlinearity (nonaffinity?) we can use the logistic function.

> logistic :: (Num r, Fractional r, Floating r) => r -> r
> logistic x = 1 / (1 + (exp (negate x)))

And applying this function pointwise:

> logisticSM
>   :: (Num r, Fractional r, Floating r) => Size -> SupervisedModel r
> logisticSM u = SM
>   { smParamSize = 0
>   , smInputSize = u
>   , smOutputSize = u
>   , smRegularize = []
>   , smFunction = F
>       { dom = 0 :+ u
>       , cod = u
>       , fun = \v -> tensor u $
>           \i -> logistic ((termR v)`at`i)
>       }
>   , smGradient = F
>       { dom = 0 :+ u
>       , cod = u :* (0 :+ u)
>       , fun = \v -> tensor (u :* (0 :+ u)) $
>           \(i :& (R j)) -> (kronecker i j) *
>             (logistic $ (termR v)`at`i) *
>             (1 - (logistic $ (termR v)`at`i))
>       }
>   }
> 
> -- type fixed for testing
> logisticSMOf
>   :: (Num r, Fractional r, Floating r) => r -> Size -> SupervisedModel r
> logisticSMOf _ = logisticSM

We can now test the composite of two logistic models, and of an affine followed by a logistic.

> _test_compose_logistic_model_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Property)
> _test_compose_logistic_model_dual_gradient r =
>   testName "compose logistic model dual gradient check" $
>   \u -> (u ~/= 0) ==>
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (dualGrad $ smFunction $
>         ((logisticSMOf (toDual r) u)) >>> (logisticSMOf (toDual r) u))
>       (smGradient $
>         (logisticSMOf r u) >>> (logisticSMOf r u))
> 
> 
> _test_compose_affine_logistic_model_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_compose_affine_logistic_model_dual_gradient r =
>   testName "compose affine logistic model dual gradient check" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (dualGrad $ smFunction $
>         ((affineSMOf (toDual r) u v)) >>> (logisticSMOf (toDual r) v))
>       (smGradient $ (affineSMOf r u v) >>> (logisticSMOf r v))

The logistic function maps $\mathbb{R}$ to the interval $(0,1)$, which is handy for training classification functions. But our sum squared error cost function is less good at training models which end with a logistic layer, precisely because the predictions and example outputs are constrained to $(0,1)$. Instead, we can use the logistic error function. If $f : \mathbb{R}^{\Theta \oplus A} \rightarrow \mathbb{R}^1$, then the logistic cost function $\mathsf{cost} : \mathbb{R}^\Theta \rightarrow \mathbb{R}$ is given by $$\mathsf{cost}(\theta) = \frac{1}{m} \sum_{i = 1}^m \left( -y_i \ln(f(\theta \oplus x_i)) - (1 - y_i) \ln(1 - f(\theta \oplus x_i)) \right),$$ where $m$ is the number of training examples, $(x_i,y_i)$ is the $i$th training example, and $f$ is the function being trained. In this case the $y$ must have size 1 and have the value 0 or 1. The gradient of logistic cost has signature $$\mathbb{R}^\Theta \rightarrow \mathbb{R}^{1 \otimes \Theta},$$ and the value of this gradient at $i \in \Theta$ is

$$\begin{eqnarray*}
 &   & \nabla(\mathsf{cost})(\theta)_{0 \& i} \\
 & = & D(\mathsf{cost}(w_{i,\theta}(x))_0)(\theta_i) \\
 & = & D\left(\frac{1}{m} \sum_{k = 1}^m \left( -y_k \ln(f(w_{i,\theta}(x) \oplus x_k)) - (1 - y_k) \ln(1 - f(w_{i,\theta}(x) \oplus x_k)) \right)\right)(\theta_i) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left( -y_k D(\ln(f(w_{i,\theta}(x) \oplus x_k)))(\theta_i) - (1 - y_k) D(\ln(1 - f(w_{i,\theta}(x) \oplus x_k)))(\theta_i) \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left( -y_k \frac{D(f(w_{i,\theta}(x) \oplus x_k))(\theta_i)}{(f(w_{i,\theta}(x) \oplus x_k))(\theta_i)} - (1 - y_k) \frac{D(1 - f(w_{i,\theta}(x) \oplus x_k))(\theta_i)}{(1 - f(w_{i,\theta}(x) \oplus x_k))(\theta_i)} \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left( -y_k \frac{D(f(w_{i,\theta}(x) \oplus x_k))(\theta_i)}{f(\theta \oplus x_k)} - (1 - y_k) \frac{- D(f(w_{i,\theta}(x) \oplus x_k))(\theta_i)}{1 - f(\theta \oplus x_k)} \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left( -y_k \frac{\nabla(f(- \oplus x_k))(\theta)_{0 \& i}}{f(\theta \oplus x_k)} - (1 - y_k) \frac{- \nabla(f(- \oplus x_k))(\theta)_{0 \& i}}{1 - f(\theta \oplus x_k)} \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left( -y_k \frac{\nabla(f(- \oplus x_k))(\theta)_{0 \& i}}{f(\theta \oplus x_k)} + (1 - y_k) \frac{\nabla(f(- \oplus x_k))(\theta)_{0 \& i}}{1 - f(\theta \oplus x_k)} \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \nabla(f(- \oplus x_k))(\theta)_{0 \& i} \left( \frac{1 - y_k}{1 - f(\theta \oplus x_k)} - \frac{y_k}{f(\theta \oplus x_k)} \right) \\
 & = & \frac{1}{m} \sum_{k = 1}^m \left(\nabla(f)(\theta \oplus x_k) \cdot \mathsf{vcat}(\mathsf{Id}_{\Theta},\mathsf{Z}_{A \otimes \Theta})\right)_{0 \& i} \left( \frac{1 - y_k}{1 - f(\theta \oplus x_k)} - \frac{y_k}{f(\theta \oplus x_k)} \right)
\end{eqnarray*}$$

> logisticError
>   :: (Num r, Fractional r, Floating r, Real r)
>   => SupervisedModel r -> CostFunction r
> logisticError model = CF
>   { cfFunction = \examples -> F
>       { dom = smParamSize model
>       , cod = 1
>       , fun = \theta ->
>           let
>             m = fromIntegral $ length examples
>             f = smFunction model
>             lg (x,y) =
>               ((negate (y`at`0)) * (log $ (f $@ (theta ⊕ x))`at`0))
>               - ((1 - (y`at`0)) * (1 - (log $ (f $@ (theta ⊕ x))`at`0)))
>           in
>             (1/m) .@ (cell $ sum $ map lg examples)
>       }
> 
>   , cfGradient = \examples -> F
>       { dom = smParamSize model
>       , cod = 1 :* (smParamSize model)
>       , fun = \theta ->
>           let
>             m = fromIntegral $ length examples
>             f = smFunction model
>             gf = smGradient model
>             a = smInputSize model
>             t = smParamSize model
>             q = (idMat t) `vcat` (zeros $ a :* t)
>             gr (x,y) = tensor (1 :* t) $ \(_ :& i) ->
>                  (((gf $@ (theta ⊕ x)) *** q)`at`(0 :& i))
>                  *
>                  (((1 - (y`at`0)) / (1 - ((f $@ (theta ⊕ x))`at`0)))
>                    -
>                  ((y`at`0) / ((f $@ (theta ⊕ x))`at`0)))
>           in
>             (1/m) .@ (vsum $ map gr examples)
>       }
>   }

And a quick test for the logistic error gradient:

> _test_logistic_model_lge_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Int -> Property)
> _test_logistic_model_lge_dual_gradient r =
>   testName "logistic model logistic error dual gradient check" $
>   \u k -> (u ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbBinaryTensorOf r 1)) $
>       \xs -> (xs /= []) ==>
>         _test_functions_equal MaxAbsDiff (10**(-4))
>           (dualGrad $ cfFunction
>             (logisticError $ logisticSMOf (toDual r) 1)
>             (map (\(x0,y0) -> (fmap toDual x0, fmap toDual y0)) xs))
>           (cfGradient
>             (logisticError $ logisticSMOf r 1) xs)
> 
> _test_linear_model_lge_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Int -> Property)
> _test_linear_model_lge_dual_gradient r =
>   testName "linear model logistic error dual gradient check" $
>   \u k -> (u ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbBinaryTensorOf r 1)) $
>       \xs -> (xs /= []) ==>
>         _test_functions_equal MaxAbsDiff (10**(-4))
>           (dualGrad $ cfFunction
>             (logisticError $ affineSMOf (toDual r) u 1)
>             (map (\(x0,y0) -> (fmap toDual x0, fmap toDual y0)) xs))
>           (cfGradient
>             (logisticError $ affineSMOf r u 1) xs)
> 
> _test_loglinear_model_lge_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Int -> Property)
> _test_loglinear_model_lge_dual_gradient r =
>   testName "loglinear model logistic error dual gradient check" $
>   \u k -> (u ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbBinaryTensorOf r 1)) $
>       \xs -> (xs /= []) ==>
>         _test_functions_equal MaxAbsDiff (10**(-4))
>           (dualGrad $ cfFunction
>             (logisticError $ affineSMOf (toDual r) u 1 >>> logisticSM 1)
>             (map (\(x0,y0) -> (fmap toDual x0, fmap toDual y0)) xs))
>           (cfGradient
>             (logisticError $ affineSMOf r u 1 >>> logisticSM 1) xs)


Tests
-----

> _test_composite_models
>   :: (Show r, Fractional r, Ord r, Num r, RealFloat r,
>       Floating r, Real r, Arbitrary r)
>   => r -> Int -> Int -> IO ()
> _test_composite_models r num size = do
>   testLabel "Composite Models"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_compose_logistic_model_dual_gradient r)
>   runTest args (_test_compose_affine_model_dual_gradient r)
>   runTest args (_test_compose_affine_logistic_model_dual_gradient r)
> 
>   runTest args (_test_logistic_model_lge_dual_gradient r)
>   chattyTest args (_test_linear_model_lge_dual_gradient r)
>   chattyTest args (_test_loglinear_model_lge_dual_gradient r)
> 
> 
> main_composite_models :: IO ()
> main_composite_models = _test_composite_models (0 :: Double) 20 3
