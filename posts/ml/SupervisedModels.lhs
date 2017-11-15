---
title: Supervised Learning Models
author: nbloomf
date: 2017-10-20
tags: ml, literate-haskell
---

Thousands of nerds have written thousands of blog posts about supervised machine learning. Here's mine. :) Caveat- this is a terrible and handwavy understanding of the motivation for supervised learning, but it works for me.

Lots of real-world data is random -- drawn from some probability distribution which is generally unknown and unknowable. But if we have some additional information we may be able to narrow down the range of <em>possible</em> distributions. A classic example is the sale price of a given house; for all practical purposes we can treat the sale price of a house as a random variable with a hideously complicated distribution. But if we have some additional information about the house -- size, age, number of bedrooms, location, frontage, and so on -- we can narrow down the distribution <em>a lot</em>. In fact experienced realtors can reliably predict the final sale price of a house to within a small margin.

That is, for at least some random data (e.g. sale price) we can think of the probability distribution itself as being a <em>function</em> of some additional input (e.g. size, location). If we knew this function, we could use it to <em>predict</em> new observations based on new input.

This doesn't sound very useful at first; we have an unknown function that returns unknowable probability distributions. But! If we have some <em>example data</em> drawn from this parameterized distribution, we can use them to narrow the range of possible functions. In other words, if we find a function that considers our example data to be reasonable, then the function itself is possibly a reasonable candidate for the underlying distribution, and so possibly useful for making predictions on <em>new</em> input.

One way to find a candidate function is to (1) guess that it has a particular form, parameterized by one or more variables, and (2) use some calculus to find the "best" values for the variables (called <em>training</em> the model).

And here's the magic. First of all, this more or less works, which is neat. But even more neat is that our guess doesn't have to be ridiculously complicated in order to make interesting and useful predictions.

In this post we'll give a more specific definition for supervised learning models. We'll also define a few specific examples, as well as a handful of "model combinators" we can use to combine simpler models into more complex ones, like an algebra of learning models.

First some boilerplate.

> {-# LANGUAGE LambdaCase #-}
> module SupervisedModels where
> 
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

Formally, a <em>supervised learning model</em> is a function on tensors which takes a tensor parameter -- that is, a function with a signature like $$M : \mathbb{R}^\Theta \rightarrow \mathbb{R}^u \rightarrow \mathbb{R}^v.$$ We'll think of this function as having signature $$M : \mathbb{R}^{\Theta \oplus u} \rightarrow \mathbb{R}^v.$$ To represent a model like this, we will keep track of the sizes of the parameter ($\Theta$), input ($u$), and output ($v$) tensors as well as the mapping ($M$). We'll also keep track of a list of indices for the so-called <em>regularized</em> parameters (more on these later). Finally, we'll also keep track of the gradient of the mapping.

> data SupervisedModel r = SM
>   { smParamSize  :: Size
>   , smInputSize  :: Size
>   , smOutputSize :: Size
>   , smRegularize :: [Index]
>   , smFunction   :: Function r
>   , smGradient   :: Function r
>   }

Importantly, with a parameter and input tensor in hand, our model can make a prediction.

> predictSM :: SupervisedModel r -> Tensor r -> Tensor r -> Tensor r
> predictSM model theta x = (smFunction model) $@ (theta `oplus` x)
> 
> gradientSM :: SupervisedModel r -> Tensor r -> Tensor r -> Tensor r
> gradientSM model theta x = (smGradient model) $@ (theta `oplus` x)

For example, one of the simplest possible models is a linear transformation or, more generally, an affine transformation. Recall that a linear transformation is a map $\mathbb{R}^u \rightarrow \mathbb{R}^v$, where $u$ and $v$ are natural numbers, which we can implement using matrix multiplication (mumble after choosing a basis mumble), and an affine transformation is a linear transformation plus a constant. So in this case our model $M$ looks like $$M((A \oplus b) \oplus x) = Ax + b,$$ where $A$ is a $v \times u$ matrix and $b$ is a $v$ vector. Or, using our tensor language, using the gradient of $MV + B$ we computed earlier:

> affineSM :: (Num r) => Size -> Size -> SupervisedModel r
> affineSM from to = SM
>   { smParamSize   = (to :* from) :+ to
>   , smInputSize   = from
>   , smOutputSize  = to
> 
>   , smRegularize  = map L $ indicesOf (to :* from)
> 
>   , smFunction = F
>       { dom = ((to :* from) :+ to) :+ from
>       , cod = to
>       , fun = \x ->
>           let
>             m = termL (termL x)
>             b = termR (termL x)
>             v = termR x
>           in
>             (m **> v) .+ b
>       }
> 
>   , smGradient = F
>       { dom = ((to :* from) :+ to) :+ from
>       , cod = to :* (((to :* from) :+ to) :+ from)
>       , fun = \x ->
>           let
>             m = termL (termL x)
>             b = termR (termL x)
>             v = termR x
>           in
>             tensor (to :* (((to :* from) :+ to) :+ from)) $
>               \case
>                 k :& (L (L (i :& j))) ->
>                   if i == k then v `at` j else 0
>                 k :& (L (R s)) ->
>                   if s == k then 1 else 0
>                 k :& (R t) ->
>                   m `at` (k :& t)
>       }
>   }
> 
> -- type-fixed version for testing
> affineSMOf :: (Num r) => r -> Size -> Size -> SupervisedModel r
> affineSMOf _ u v = affineSM u v

(Again, ignore the ``smRegularize`` parameter for now.)

The most important constraint that a ``SupervisedModel`` should satisfy is that ``smGradient`` be the gradient of ``smFunction``. We can check this using both the numerical and dual number strategies because why not.

> _test_affine_model_numerical_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_affine_model_numerical_gradient r =
>   testName "affine model numerical gradient check" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (approxGrad (10**(-5)) $ smFunction $ affineSMOf r u v)
>       (smGradient $ affineSMOf r u v)
> 
> _test_affine_model_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_affine_model_dual_gradient r =
>   testName "affine model dual gradient check" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (dualGrad $ smFunction $ affineSMOf (toDual r) u v)
>       (smGradient $ affineSMOf r u v)


Training
--------

So our model takes a parameter and returns a function that makes predictions. To <em>train</em> the model, we first choose some method, called a <em>cost function</em>, for measuring how bad its predictions are for a given parameter; generally a function from $\mathbb{R}^\Theta$ to $\mathbb{R}$. There are many possible choices for the cost function, so we'll represent them with a type. Generally the cost function will depend on the model being used, and should take (1) a set of training examples $\{x_i,y_i\}_{i \in T} \subseteq \mathbb{R}^u \times \mathbb{R}^v$ and (2) a parameter $\theta \in \mathbb{R}^\Theta$, and return a measure of how badly $M$ performs on the $(x_i,y_i)$ under $\theta$. We'll also keep track of the gradient of the cost function.

> data CostFunction r = CF
>   { cfFunction 
>       :: [(Tensor r, Tensor r)] -> Function r
>   , cfGradient
>       :: [(Tensor r, Tensor r)] -> Function r
>   }

One simple but useful cost function is the sum-squared-error function. If our training set is $\{(x_i,y_i\}_{i=1}^m$, the sum-squared-error cost function is given by $$\mathsf{cost}(\theta) = \frac{1}{2m} \sum_{i=1}^m ||f(\theta \oplus x_i) - y_i||^2,$$ where $||\ast||^2$ is the dot square of a tensor. In code:

> sumSquaredError
>   :: (Num r, Fractional r, Real r)
>   => SupervisedModel r -> CostFunction r
> sumSquaredError model = CF
>   { cfFunction = \examples -> F
>       { dom = smParamSize model
>       , cod = 1
>       , fun = \theta ->
>           let
>             m = fromIntegral $ length examples
>             f = smFunction model
>             ns (x,y) = normSquared (((f $@ (theta `oplus` x)) .- y))
>           in
>             cell $ (sum $ map ns examples) / (2*m)
>       }
> 
>   , cfGradient = \examples -> F
>       { dom = smParamSize model
>       , cod = smParamSize model
>       , fun = \theta ->
>           let
>             m = fromIntegral $ length examples
>             f = smFunction model
>             g = smGradient model
>             gr (x,y) =
>               ((f $@ (theta `oplus` x)) .- y)
>                 <** (g $@ (theta `oplus` x))  -- vector-matrix product
>           in
>             termL $ (1/m) .@ (vsum $ map gr examples)
>       }
>   }

Why is this useful? There are good theoretical reasons which I do not totally understand. But on a practical level sum squared error is simple and nicely differentiable and intuitively a good measure of "closeness". All terms in the sum are positive, and each term contributes less to the sum when $f(\theta \oplus x_i)$ (the prediction) and $y_i$ (the actual observation) are close.

We should test that the sum squared error cost function gradient is reasonable.

> _test_affine_model_sse_numerical_gradient
>   :: (Eq r, Ord r, Num r, Fractional r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Int -> Property)
> _test_affine_model_sse_numerical_gradient r =
>   testName "affine model sum squared error numerical gradient check" $
>   \u v k -> (u ~/= 0) && (v ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbTensorOf r v)) $
>       \xs -> (xs /= []) ==>
>         _test_functions_equal MaxRelDiff (10**(-2))
>           (approxGrad (10**(-4)) $
>             cfFunction (sumSquaredError $ affineSMOf r u v) xs)
>           (cfGradient (sumSquaredError $ affineSMOf r u v) xs)
> 
> _test_affine_model_sse_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Int -> Property)
> _test_affine_model_sse_dual_gradient r =
>   testName "affine model sum squared error dual gradient check" $
>   \u v k -> (u ~/= 0) && (v ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbTensorOf r v)) $
>       \xs -> (xs /= []) ==>
>         _test_functions_equal MaxAbsDiff (10**(-6))
>           (dualGrad $ cfFunction
>             (sumSquaredError $ affineSMOf (toDual r) u v)
>             (map (\(h,k) -> (fmap toDual h, fmap toDual k)) xs))
>           (cfGradient (sumSquaredError $ affineSMOf r u v) xs)

With a cost function in hand, we can use gradient descent to minimize it. ``smSimpleTrain`` takes a cost function, a list of example data, an initial guess, and a learning rate, and attempts to minimize the cost function.

> smSimpleTrain
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r)
>   => CostFunction r
>   -> [(Tensor r, Tensor r)]
>   -> Tensor r
>   -> r
>   -> Tensor r
> smSimpleTrain cost examples x0 lr =
>   gradDesc (cfGradient cost $ examples) x0 x0
>     (maxAbsDiffLessThan (10**(-15)))
>     (fixedLearningRate lr)

As a smell test we can try to learn a known function. We'll do this by hand with a couple of examples and then generalize to a test.

First, consider a training set with two examples, each of which is a pair of size 1 tensors -- in other words, two ordered pairs of real numbers $(x_1,y_1)$ and $(x_2,y_2)$. For simplicity let's say they are $(1,1)$ and $(2,2)$.

> smell_test_data_1 :: (Num r) => [(Tensor r, Tensor r)]
> smell_test_data_1 =
>   [ (cell 1, cell 1)
>   , (cell 2, cell 2)
>   ]

An affine model compatible with these data must have signature $$f : \mathbb{R}^{((1 \otimes 1) \oplus 1) \oplus 1} \rightarrow \mathbb{R}^1$$ and looks something like $$f((m \oplus b) \oplus x) = mx + b,$$ where $m$ and $b$ are the trainable parameters. In this case the test data can be fit exactly (which is not normally desirable, but we're just testing here) with the parameters $m = 1$ and $b = 0$.

> smell_test_model_1 :: (Num r) => SupervisedModel r
> smell_test_model_1 = affineSM 1 1

And we can train this model to find a locally optimal value for the parameter tensor:

> smell_test_theta_1
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Real r)
>   => Tensor r
> smell_test_theta_1 = smSimpleTrain
>   (sumSquaredError smell_test_model_1)
>   smell_test_data_1
>   (zeros $ smParamSize $ smell_test_model_1)
>   0.15

Sure enough, we have

```haskell
$> smell_test_theta_1
   0.9999999999999443
9.036826666597734e-14
```

which is pretty close to $m = 1$ and $b = 0$. Moreover, we can use this ``theta`` to make predictions.

> smell_test_predict_1
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Real r)
>   => Tensor r -> Tensor r
> smell_test_predict_1 x =
>   predictSM smell_test_model_1 smell_test_theta_1 x

with:

```haskell
$> smell_test_predict_1 (cell 1)
1.0000000000000346
$> smell_test_predict_1 (cell 2)
1.999999999999979
$> smell_test_predict_1 (cell 150)
149.99999999999173
```

Woo! It doesn't not work. :)

While we're at it, here's a slightly more complicated example.

> smell_test_data_2 :: (Num r) => [(Tensor r, Tensor r)]
> smell_test_data_2 =
>   [ (vec [0,1,2], cell 1)
>   , (vec [2,4,1], cell 2)
>   , (vec [3,2,2], cell 0)
>   , (vec [2,1,0], cell 2)
>   ]
> 
> smell_test_model_2 :: (Num r) => SupervisedModel r
> smell_test_model_2 = affineSM 3 1
> 
> smell_test_theta_2
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Real r)
>   => Tensor r
> smell_test_theta_2 = smSimpleTrain
>   (sumSquaredError smell_test_model_2)
>   smell_test_data_2
>   (zeros $ smParamSize $ smell_test_model_2)
>   0.15
> 
> smell_test_predict_2
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Real r)
>   => Tensor r -> Tensor r
> smell_test_predict_2 x =
>   predictSM smell_test_model_2 smell_test_theta_2 x


Regularization
--------------

So training a model boils down to finding a parameter $\theta$ that minimizes the cost function. It turns out that we sometimes have occasion to want additional constraints on the parameters; say, by preferring that they not be too large. For example, at the moment we only know how to deal with linear and affine models, but even these can model nonlinear functions if we introduce new inputs to represent nonlinear combinations of the old inputs. If we have a data set that naturally has one input, $x$, we could try to learn a function of $x$ like $$f(m,b,x) = mx + b$$ or we could learn a function of $x$ and $x^2$ like $$f(a,m,b,x) = ax^2 + mx + b,$$ or a function of $\sqrt{x}$, or $\log(x)$, or any number of other possibilities. This opens a wide range of more interesting nonlinear functions, but also increases the risk of overfitting. To prevent this, we can penalize parameters which are large in absolute value -- doing so helps because when data is fit "unnaturally" by a complex nonlinear function the coefficients tend to be large. We can do this by adding the square of each parameter to the cost function. Of course we don't necessarily want to penalize *all* parameters; for instance, in the affine model the offset parameters $B$ have no effect on any polynomial inputs we introduce.

> regularize
>   :: (Num r, Fractional r, Real r)
>   => r -> SupervisedModel r -> CostFunction r -> CostFunction r
> regularize lambda model cost = CF
>   { cfFunction = \examples -> F
>       { dom = smParamSize model
>       , cod = 1
>       , fun = \theta ->
>           let
>             reg = sum [ (theta `at` i)^2 | i <- smRegularize model ]
>             m = fromIntegral $ length $ smRegularize model
>           in
>             (cfFunction cost examples $@ theta)
>               .+ (cell $ lambda * reg / m)
>       }
> 
>   , cfGradient = \examples -> F
>       { dom = smParamSize model
>       , cod = smParamSize model
>       , fun = \theta ->
>           let
>             m = fromIntegral $ length $ smRegularize model
>             rg = tensor (smParamSize model) $
>               \i -> if i `elem` smRegularize model
>                 then 2 * lambda * (theta`at`i) / m
>                 else 0
>           in
>             (cfGradient cost examples $@ theta) .+ rg
>       }
>   }

We should test that the regularized sum squared error cost function gradient is reasonable for affine models.

> _test_affine_model_regularized_sse_numerical_gradient
>   :: (Eq r, Ord r, Num r, Fractional r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Int -> Property)
> _test_affine_model_regularized_sse_numerical_gradient r =
>   testName "affine model regularized sse numerical gradient check" $
>   \u v k -> (u ~/= 0) && (v ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbTensorOf r v)) $
>       \xs lam -> (xs /= []) ==>
>         let
>           m = affineSMOf r u v
>         in
>           _test_functions_equal MaxRelDiff (10**(-1))
>             (approxGrad (10**(-4)) $
>               cfFunction (regularize (abs lam) m $ sumSquaredError m) xs)
>             (cfGradient (regularize (abs lam) m $ sumSquaredError m) xs)
> 
> _test_affine_model_regularized_sse_dual_gradient
>   :: (Eq r, Ord r, Num r, Fractional r,
>        Floating r, Real r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Int -> Property)
> _test_affine_model_regularized_sse_dual_gradient r =
>   testName "affine model regularized sse dual gradient check" $
>   \u v k -> (u ~/= 0) && (v ~/= 0) && (k /= 0) ==>
>     forAll (vectorOf k $ pairOf (arbTensorOf r u) (arbTensorOf r v)) $
>       \xs lam -> (xs /= []) ==>
>         let
>           m1 = affineSMOf (toDual r) u v
>           m2 = affineSMOf r u v
>         in
>           _test_functions_equal MaxAbsDiff (10**(-6))
>             (dualGrad $ cfFunction
>               (regularize (toDual $ abs lam) m1 $ sumSquaredError m1)
>               (map (\(h,k) -> (fmap toDual h, fmap toDual k)) xs))
>             (cfGradient
>               (regularize (abs lam) m2 $ sumSquaredError m2) xs)


Test Suite
----------

> _test_supervised_models
>   :: (Show r, Fractional r, Ord r, Num r,
>        Floating r, Real r, Arbitrary r)
>   => r -> Int -> Int -> IO ()
> _test_supervised_models r num size = do
>   testLabel "Supervised Models"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_affine_model_dual_gradient r)
>   runTest args (_test_affine_model_numerical_gradient r)
> 
>   runTest args (_test_affine_model_sse_dual_gradient r)
>   runTest args (_test_affine_model_sse_numerical_gradient r)
> 
>   runTest args (_test_affine_model_regularized_sse_dual_gradient r)
>   runTest args (_test_affine_model_regularized_sse_numerical_gradient r)
> 
> 
> main_supervised_models :: IO ()
> main_supervised_models = _test_supervised_models (0 :: Double) 30 3
