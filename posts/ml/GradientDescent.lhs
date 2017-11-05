---
title: Optimization by Gradient Descent
author: nbloomf
date: 2017-10-19
tags: ml, literate-haskell
---

Boilerplate.

> module GradientDescent where
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

Now that we know how to find the gradient of a function, we can use it to optimize the function using *gradient descent*. The intuition here is that the gradient of a function at a point gives the direction of steepest ascent there, so the negative of the gradient gives the direction of steepest descent -- the direction an $n$-dimensional marble would roll if released from rest.

The basic method goes something like this: we start with an initial guess $v_0$, then update the guess using the recurrence $$v_{n+1} = v_n - \alpha \nabla(f)(v_n),$$ where $f$ is the function to be minimized and $\alpha$ is some number (not necessarily constant) called the *learning rate*. At some point we decide to stop, and the last update $v_n$ should be at least a local minimum of $f$.

This paragraph is simple enough, but a lot of questions remain. How is $\alpha$ determined, and should it change between iterations? How do we decide when to stop? These are questions without unique answers. But we can fill in the structure of the gradient descent algorithm without knowing them.

Say we have some type ``st`` representing the "state" of a gradient descent process at a given time. Say further that we have some function ``st -> r`` that gives the learning rate, and a function ``Tensor r -> st -> Maybe st`` that decides to stop the iteration (by returning ``Nothing``) or to keep going (by returning a new state). Then gradient descent looks something like this.

> gradDesc
>   :: (Num r)
>   => Function r                   -- gradient
>   -> st                           -- initial state
>   -> Tensor r                     -- initial guess
>   -> (Tensor r -> st -> Maybe st) -- update state or stop
>   -> (st -> r)                    -- learning rate
>   -> Tensor r
> 
> gradDesc g st0 x0 update rate =
>   let
>     next st v = v .- ((rate st) .@ (g $@ v))
> 
>     step st x =
>       let y = next st x in
>       case update y st of
>         Nothing -> y
>         Just w  -> step w y
>   in
>     step st0 x0

To turn this into an actual gradient descent algorithm, we need some specific functions we can plug in for the update and learning rate. For instance, it's reasonable to use a fixed learning rate.

> fixedLearningRate :: (Num r) => r -> a -> r
> fixedLearningRate alpha _ = alpha

And one particularly simple (if not super useful) state might be to keep track of the number of steps taken so far, and stop when that number reaches a limit.

> fixedNumSteps
>   :: Int -> Tensor r -> Int -> Maybe Int
> fixedNumSteps m _ k = if k >= m
>   then Nothing
>   else Just (k+1)

Now if ``f`` is a tensor function and ``v`` a tensor,

```haskell
gradDesc f 0 v (fixedNumSteps 100) (fixedLearningRate 0.5)
```

Carries out gradient descent for 100 steps with learning rate 0.5. A more practical update function keeps track of the last iteration and stops when the difference between it and the current value is less than some threshold.

> maxAbsDiffLessThan
>   :: (Eq r, Ord r, Num r, Fractional r)
>   => r -> Tensor r -> Tensor r -> Maybe (Tensor r)
> maxAbsDiffLessThan eps x y =
>   let
>     del = distanceBy MaxAbsDiff x y
>   in
>     if del < eps
>       then Nothing
>       else Just x

As a really simple example, fix a vector $v \in \mathbb{R}^s$ and consider the function $f : \mathbb{R}^s \rightarrow \mathbb{R}^s$ given by $$f(x)_i = (x_i - v_i)^2.$$ This is quadratic in each coordinate with minimum at $x_i = v_i$. Moreover this function is convex, so that minimum is unique, and gradient descent should find it regardless of the initial guess.

> _test_grad_desc_line
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Show r, Arbitrary r)
>   => r -> Test (Size -> Property)
> _test_grad_desc_line r =
>   testName "grad desc line" $
>     \u -> u ~/= 0 ==>
>       forAll2 (arbTensorOf r u) (arbTensorOf r u) $
>         \v x0 ->
>           let
>             g = (idF u) .- (constF u v)
>             w = gradDesc g x0 x0 
>                   (maxAbsDiffLessThan (10**(-8)))
>                   (fixedLearningRate 0.7)
>           in
>             (distanceBy MaxAbsDiff v w) < (10**(-6))


Tests
-----

> _test_gradient_descent
>   :: (Eq r, Ord r, Num r, Fractional r, Floating r, Show r, Arbitrary r)
>   => r -> Int -> Int -> IO ()
> _test_gradient_descent r num size = do
>   testLabel "Gradient Descent"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_grad_desc_line r)
> 
> main_gradient_descent :: IO ()
> main_gradient_descent = _test_gradient_descent (0::Double) 100 5
