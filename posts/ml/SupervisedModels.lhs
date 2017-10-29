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



> {-# LANGUAGE ScopedTypeVariables #-}
> module SupervisedModels where
> 
> import Indices
> import Tensors
> import Gradients

> {-

Models
------

Formally, a <em>supervised learning model</em> is a function on tensors which takes a tensor parameter -- that is, a function with a signature like $$M : \mathbb{R}^\Theta \rightarrow \mathbb{R}^u \rightarrow \mathbb{R}^v.$$ To represent a model like this, we will keep track of the sizes of the parameter ($\Theta$), input ($u$), and output ($v$) tensors as well as the mapping ($M$). We'll also keep track of a list of indices for the so-called <em>regularized</em> parameters (more on these later). Finally, for reasons we'll see later, we'll also keep track of the gradient of the mapping as a function of its parameter; that is, $\nabla(M(-)(x))(\theta)$.

> data Model r = M
>   { paramSize   :: Size
>   , inputSize   :: Size
>   , outputSize  :: Size
>   , regularized :: [Index]
>   , function    :: Tensor r -> Tensor r -> Tensor r
>   , flipGrad    :: Tensor r -> Tensor r -> Tensor r
>   }

For example, one of the simplest possible models is a linear transformation or, more generally, an affine transformation. Recall that a linear transformation is a map $\mathbb{R}^u \rightarrow \mathbb{R}^v$, where $u$ and $v$ are natural numbers, which we can implement using matrix multiplication (mumble after choosing a basis mumble), and an affine transformation is a linear transformation plus a constant. So in this case our model $M$ looks like $$M(A)(x) = Ax + b,$$ where $A$ is a $v \times u$ matrix and $b$ is a $v$ vector. Or, using our tensor language:

> affineModel :: (Num r) => Size -> Size -> Model r
> affineModel from to = M
>   { paramSize   = (to :* from) :+ to
>   , inputSize   = from
>   , outputSize  = to
> 
>   , regularized = map L $ indicesOf (to :* from)
> 
>   , function = \theta x ->
>       let
>         m = termL theta
>         b = termR theta
>       in (contract m x) .+ b
> 
>   , flipGrad = \x _ ->
>       tensor (to :* (to :* from)) $
>         \(t :& (k :& h)) ->
>           if t == k
>             then x `at` h
>             else 0
>   }

(Again, ignore the ``regularized`` field for now.) We computed that gradient in the last post.

So our model takes a parameter and returns a function that makes predictions. To <em>train</em> the model, we first choose some method, called a <em>cost function</em>, for measuring how bad its predictions are for a given parameter; generally a function from $\mathbb{R}^\Theta$ to $\mathbb{R}$. There are many possible choices for the cost function, so we'll make it a type synonym. A cost function should take (1) a set of training examples $\{x_i,y_i\}_{i \in T} \subseteq \mathbb{R}^u \times \mathbb{R}^v$, (2) a model $M$, and (3) a parameter $\theta \in \mathbb{R}^\Theta$, and return a measure of how badly $M$ performs on the $(x_i,y_i)$ under $\theta$.

> data CostFunction r = CF
>   { cost     :: Model r -> [(Tensor r, Tensor r)] -> Tensor r -> r
>   , costGrad :: Model r -> [(Tensor r, Tensor r)] -> Tensor r -> Tensor r
>   }

One simple but useful cost function is the sum-squared-error function. If our training set is $\{(x_i,y_i\}_{i=1}^m$, the sum-squared-error cost function is given by $$\mathsf{cost}(\theta) = \frac{1}{2m} \sum_{i=1}^m ||f(\theta)(x_i) - y_i||^2,$$ where $||\ast||^2$ is the dot square of a tensor. In code:

> sumSquaredError :: (Num r, Real r, Fractional r) => CostFunction r
> sumSquaredError = CF
>   { cost = \model trainingData parameters ->
>       let
>         m = fromIntegral $ length trainingData
>         f = function model
>         k (x,y) = normSquared ((f parameters x) .- y)
>       in
>         (sum $ map k trainingData) / (2*m)
> 
>   , costGrad = \model trainingData parameters ->
>       let
>         m = fromIntegral $ length trainingData
>         f = function model
>         g = flipGrad model
>         k (x,y) = ((f parameters x) .- y) `collapseL` (g x parameters)
>       in
>         (1/m) .@ (foldr1 (.+) $ map k trainingData)
>   }

Why is this useful? There are good theoretical reasons, which I do not totally understand. But on a practical level sum squared error is simple and differentiable (useful in a moment) and intuitively a good measure of "closeness". All terms in the sum are positive, and each term contributes less to the sum when $f(\theta)(x_i)$ (the prediction) and $y_i$ (the actual observation) are close.

Then we choose a method to minimize the cost function, which takes the size of the input and output tensors as parameters because reasons.

> type Optimizer r
>   = Size -> Size -> (Tensor r -> r) -> (Tensor r -> Tensor r) -> Tensor r

And now to train the model on a given training set, we simply optimize the cost function. 

> train
>   :: Model r
>   -> CostFunction r
>   -> Optimizer r
>   -> [(Tensor r, Tensor r)]
>   -> Tensor r
> train model cf optimize trainingData
>   = optimize (inputSize model) (outputSize model) ((cost cf) model trainingData) ((costGrad cf) model trainingData)


 > gradientDescent :: (Num r) => r -> Tensor r -> (Tensor r -> Tensor r -> Bool) -> Optimizer r
 > gradientDescent rate init stop inSize outSize f =
 >   gradDesc init (step init)
 >     where
 >       step :: Tensor r -> Tensor r
 >       step theta = theta -- .- (rate .@ (gradT inSize f theta))
 > 
 >       gradDesc :: (Num r) => Tensor r -> Tensor r -> Tensor r
 >       gradDesc last next = if True == stop last next
 >         then next
 >         else gradDesc next (step next)

> compose :: Model r -> Model r -> Model r
> compose mB mA =
>   if (inputSize mB) == (outputSize mA)
>     then M
>       { paramSize   = (paramSize mB) :+ (paramSize mA)
>       , inputSize   = inputSize mA
>       , outputSize  = outputSize mB
>       , regularized = (map L $ regularized mB) ++ (map R $ regularized mA)
>       , function    = \p -> (function mB (termL p)) . (function mA (termR p))
>       , flipGrad    = undefined
>       }
>     else error "size mismatch."

> regularize :: (Real r, Fractional r) => r -> CostFunction r -> CostFunction r
> regularize lambda f = CF
>   { cost = \model trainingData parameters ->
>       let
>         reg = sum [ (parameters `at` i)^2 | i <- regularized model ]
>         m = fromIntegral $ length $ regularized model
>       in
>         ((cost f) model trainingData parameters) + (lambda * reg / m)
>   , costGrad = undefined
>   }

> func :: [(Tensor r, Tensor r)] -> Model r -> CostFunction r -> Tensor r
> func trainingData model = undefined

> -}


