---
title: Gradient Checking
author: nbloomf
date: 2017-10-18
tags: ml, literate-haskell
---

Boilerplate.

> module GradientChecking where
> 
> import Control.Applicative
> import Test.QuickCheck hiding (Function)
> import Test.QuickCheck.Test
> 
> import Indices
> import IndexIsos
> import Tensors
> import TensorFunctions
> import Gradients

Computing gradients of multivariate $f$ is intricate, so it'd be nice to have a simple (if slow) way to check them for reasonableness. In this post we'll see two methods for doing exactly that.


Numerical Approximation
-----------------------

In the single variable case the gradient at a point $v$ is the slope of the line tangent to $f$ at $v$, which can be approximated using the slope of the secant line passing through the points on $f$ at $v \pm \varepsilon$ for small epsilon, sometimes called the <em>difference quotient</em>. In math notation, the difference quotient is $$\frac{f(v + \varepsilon) - f(v - \varepsilon)}{2 \varepsilon},$$ and in code we say:

> diffquo :: (Num r, Fractional r) => (r -> r) -> r -> r -> r
> diffquo f x eps = ((f $ x + eps) - (f $ x - eps)) / (2*eps)

Of course the gradient is a bunch of pointwise univariate derivatives, so we can approximate the gradient pointwise.

> approxGrad
>   :: (Num r, Fractional r)
>   => r          -- pointwise epsilon
>   -> Function r -- function to approximate
>   -> Function r -- gradient
> 
> approxGrad eps f = F
>   { dom = dom f
>   , cod = (cod f) :* (dom f)
>   , fun = \v ->
>       let
>         g i j x  = (f $@ (inj i v x))`at`j
>       in
>         tensor ((cod f) :* (dom f)) $
>           \(j :& i) -> diffquo (g i j) (v`at`i) eps
>   }
>   where
>     inj :: (Num r) => Index -> Tensor r -> r -> Tensor r
>     inj k a@(T u _) x = tensor u $
>       \i -> if i == k then x else a`at`i

So ``approxGrad`` computes the numerical gradient of a function using some tolerance ``eps``. Testing it out by hand:

```haskell
$> let f = pointwiseF 3 sin
$> let g = approxGrad 0.00001 f
$> g $@ (vec [0,pi/2,pi])
 0.9999999999833332                 0.0                 0.0
                0.0                 0.0                 0.0
                0.0                 0.0 -0.9999999999898844
```

Which is not terrible.

If we have some other function that claims to compute the gradient, a decent reasonableness check is to see whether the numerical gradient at $v$ and the "exact" gradient at $v$ are equal, or, more likely, very close to each other. "Very close" for tensors can be measured in a few ways, each appropriate in different cases. We'll use a type to toggle among them.

> data Metric
>   = MaxAbsDiff -- max entrywise absolute difference
>   | MaxRelDiff -- max entrywise relative difference
>   deriving (Eq, Show)
> 
> 
> distanceBy
>   :: (Num r, Ord r, Fractional r, RealFloat r)
>   => Metric -> Tensor r -> Tensor r -> r
> 
> distanceBy m a b = if a==b then 0 else case m of
>   MaxAbsDiff -> maximum $ tzipWith f a b
>     where
>       f x y = if isNaN x || isNaN y
>         then 0
>         else abs (x - y)
> 
> 
>   MaxRelDiff -> maximum $ tzipWith f a b
>     where
>       f x y = if isNaN x || isNaN y
>         then 0
>         else abs $ (x - y) / (max x y)

And a helper test for function equality:

> _test_functions_equal
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => Metric -> r -> Function r -> Function r -> Property
> _test_functions_equal metric eps f g =
>   forAll (arbTensorOf eps (dom f)) $
>     \v ->
>       let
>         a = f $@ v
>         b = g $@ v
>       in
>         if distanceBy metric a b < eps
>           then True
>           else error $ concat
>             -- helps with debugging
>             [ "Functions not equal at\n" ++ show v ++ "\n"
>             , "values are\n" ++ show a ++ "\nand\n" ++ show b
>             , "\nthere."
>             ]

For example, the gradient of scalar multiplication should be a scalar multiple of the "identity" tensor; the following test verifies this.

> _test_numerical_scalar_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, Floating r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> r -> Property)
> 
> _test_numerical_scalar_gradient _ =
>   testName "numerical scalar gradient" $
>   \u k -> u ~/= 0 ==> 
>     _test_functions_equal MaxAbsDiff (10**(-6))
>       (approxGrad (10^^(-6)) $ scalarF u k)
>       (constF u (k .@ (idMat u)))

More generally, the gradient of a "linear" tensor function is a constant.

> _test_numerical_linear_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> 
> _test_numerical_linear_gradient r =
>   testName "numerical linear gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf r (v :* u)) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (approxGrad (10^^(-5)) $ linearF m)
>           (constF u m)

Yet more generally still, the gradient of an "affine" tensor function is a constant.

> _test_numerical_affine_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> 
> _test_numerical_affine_gradient r =
>   testName "numerical affine gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll2 (arbTensorOf r (v :* u)) (arbTensorOf r v) $
>       \m b ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (approxGrad (10^^(-5)) $ affineF m b)
>           (constF u m)

Pointwise functions (parameterized on the metric):

> _test_numerical_pointwise_gradient_by
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => Metric -> String -> r -> (r -> r) -> (r -> r)
>   -> Test (Size -> Property)
> 
> _test_numerical_pointwise_gradient_by metric str r p q =
>   testName ("numerical pointwise gradient (" ++ str ++ ")") $
>   \u -> u ~/= 0 ==> 
>     _test_functions_equal metric (10^^(-4))
>       (approxGrad (10^^(-4)) $ pointwiseF u p)
>       (diagF u $. (pointwiseF u q))

The gradient of direct summing is constant.

> _test_numerical_direct_sum_left_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_numerical_direct_sum_left_gradient r =
>   testName "direct sum on left numerical gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf r v) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-2))
>           (approxGrad (10^^(-6)) $ dSumL u m)
>           (constF u $ (zeros $ v :* u) ~-~ (idMat u))
> 
> _test_numerical_direct_sum_right_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_numerical_direct_sum_right_gradient r =
>   testName "direct sum on right numerical gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf r v) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-2))
>           (approxGrad (10^^(-6)) $ dSumR u m)
>           (constF u $ (idMat u) ~-~ (zeros $ v :* u))


Dual Numbers
------------

Another neat trick for computing the gradient of a function is automatic differentiation using <em>dual numbers</em>. For the single variable case, this method works by embedding $\mathbb{R}$ in the ring $\mathbb{R}[x]/(x^2)$. Given $a + bx$ in this ring, $a$ is called the <em>real part</em> and $b$ the <em>infinitesimal part</em>. Carrying out arithmetic as usual makes $b$ act like the derivative of $a$. I won't go into the details, mostly because they're a little bit magic to me still, but this can be extended to the multivariate case, as we'll do.

Remember that the gradient of a tensor function is again a tensor. So rather than keeping track of a number and its derivative, we'll keep track of a number and its gradient tensor.

> data Dual r
>   = D r (Tensor r)
>   deriving (Show)
> 
> -- we'll think of the empty gradient as
> -- representing a constant of any size.
> toDual :: r -> Dual r
> toDual x = D x empty
> 
> unDual :: Dual r -> r
> unDual (D x _) = x

Thinking of a tensor as a "variable", we dualize by embedding each coordinate with its partial derivative.

> dualize :: (Num r) => Tensor r -> Tensor (Dual r)
> dualize a@(T u _) = tensor u (\i -> var u i (a`at`i))
>   where
>     var :: (Num r) => Size -> Index -> r -> Dual r
>     var u k r = D r (tensor u (\i -> if i == k then 1 else 0))

Now we define arithmetic on dual numbers in a way that essentially encodes the chain rule at each step. With the magic of type classes, now anytime we define a function with signature ``(Num r) => Function r``, it can be evaluated over the dual numbers with no changes.

> instance (Eq r) => Eq (Dual r) where
>   (D x _) == (D y _) = x == y
> 
> 
> instance (Num r) => Num (Dual r) where
>   fromInteger x = toDual (fromInteger x)
> 
>   (D x dx) + (D y dy)
>     | (size dx) ~= 0 = D (x + y) dy
>     | (size dy) ~= 0 = D (x + y) dx
>     | otherwise      = D (x + y) (dx .+ dy)
> 
>   (D x dx) * (D y dy)
>     | (size dx) ~= 0 = x .@ (D y dy)
>     | (size dy) ~= 0 = y .@ (D x dx)
>     | otherwise      = D (x * y) ((y .@ dx) .+ (x .@ dy))
> 
>   negate (D x dx) = D (negate x) (fmap negate dx)
> 
>   abs (D x dx) = D (abs x) ((signum x) .@ dx)
> 
>   signum (D x dx) = D (signum x) (0 .@ dx)
> 
> 
> instance Vector Dual where
>   r .@ (D x dx) = D (r*x) (fmap (r*) dx)
>   (.+) = (+)
>   neg = negate
> 
> 
> instance (Eq r, Num r, Ord r) => Ord (Dual r) where
>   (D x _) <= (D y _) = x <= y
> 
>   max (D x dx) (D y dy) = if x >= y
>     then D x dx else D y dy
> 
>   min (D x dx) (D y dy) = if x <= y
>     then D x dx else D y dy
> 
> 
> instance (Eq r, Num r, Fractional r) => Fractional (Dual r) where
>   fromRational x = toDual (fromRational x)
> 
>   recip (D x dx@(T u _)) = D (1/x) ((-1/x^2) .@ dx)
> 
> 
> instance (Eq r, Num r, Floating r) => Floating (Dual r) where
>   pi             = D pi        empty
>   sqrt  (D x dx) = D (sqrt x)  ((1 / (2*(sqrt x))) .@ dx)
>   exp   (D x dx) = D (exp x)   ((exp x) .@ dx)
>   log   (D x dx) = D (log x)   ((1 / x) .@ dx)
>   sin   (D x dx) = D (sin x)   ((cos x) .@ dx)
>   cos   (D x dx) = D (cos x)   ((-(sin x)) .@ dx)
>   tan   (D x dx) = D (tan x)   ((1/(cos x)**2) .@ dx)
>   asin  (D x dx) = D (asin x)  ((1/(sqrt(1-x**2))) .@ dx)
>   acos  (D x dx) = D (acos x)  ((-1/(sqrt(1-x**2))) .@ dx)
>   atan  (D x dx) = D (atan x)  ((1/(1+x**2)) .@ dx)
>   sinh  (D x dx) = D (sinh x)  ((cosh x) .@ dx)
>   cosh  (D x dx) = D (cosh x)  ((sinh x) .@ dx)
>   tanh  (D x dx) = D (tanh x)  ((1-(tanh x)**2) .@ dx)
>   asinh (D x dx) = D (asinh x) ((1/(sqrt(x**2+1))) .@ dx)
>   acosh (D x dx) = D (acosh x) ((1/(sqrt(x**2-1))) .@ dx)
>   atanh (D x dx) = D (atanh x) ((1/(1-x**2)) .@ dx)
> 
>   (D x dx) ** (D y dy)
>     | dx == empty = D (x**y) ((x**y) .@ ((log x) .@ dy))
>     | dy == empty = D (x**y) ((x**y) .@ ((y/x) .@ dx))
>     | otherwise   = D (x**y)
>         ((x**y) .@ (((log x) .@ dy) .+ ((y/x) .@ dx)))
> 
>   logBase (D x _) (D y dy) = D (logBase x y)
>     ((1/(log x)**2) .@ ((((log y)/x) .@ dy) .- (((log x)/y) .@ dy)))
> 
> instance (Real r) => Real (Dual r) where
>   toRational (D x _) = toRational x

Now we can automatically take a tensor function on (tensors of) dual numbers, and find its gradient as a function on (tensors of) ordinary numbers.

> dualGrad :: (Num r)
>   => Function (Dual r) -> Function r
> dualGrad f = F
>   { dom = dom f
>   , cod = (cod f) :* (dom f)
>   , fun = \v -> tensor ((cod f) :* (dom f)) $
>       \(i :& j) ->
>         let (D _ dx) = (f $@ (dualize v)) `at` i
>         in dx `at` j
>   }

To be clear: we can now evaluate the gradient of an arbitrary tensor function. As a quick hand test:

```haskell
$> let f = pointwiseF 1 sin -- f(x) = sin(x)
$> let g = dualGrad f -- magic
$> g $@ (cell pi)
-1.0
$> let f = pointwiseF 3 (^2) -- f(x,y,z) = (x^2,y^2,z^2)
$> let g = dualGrad f -- magic
$> g $@ (vec [1,2,3])
2 0 0
0 4 0
0 0 6
```

I will probably never get used to that. Anyway, like we did with numeric differentiation, we can use automatic differentiation to test a claimed "exact" gradient. By the way -- AD gives us the exact gradient, so why don't we just use it? Unfortunately AD ends up doing a lot of work to keep track of those intermediate derivatives, so a dedicated gradient function (if we can find it) can be more efficient. But we can still test our handwritten gradients against the AD gradient or numeric gradient on small functions to gain confidence that we're doing it right.

We need an ``Arbitrary`` instance for dual numbers:

> instance (Arbitrary r) => Arbitrary (Dual r) where
>   arbitrary = do
>     x <- arbitrary
>     return $ D x empty

And we can compare an alleged gradient function against the automatically computed gradient.

> _test_dual_scalar_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Dual r -> Property)
> _test_dual_scalar_gradient _ =
>   testName "dual scalar gradient" $
>   \u k -> u ~/= 0 ==> 
>     _test_functions_equal MaxAbsDiff (10^^(-6))
>       (dualGrad $ scalarF u k)
>       (constF u ((unDual k) .@ (idMat u)))
> 
> 
> _test_dual_linear_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_dual_linear_gradient r =
>   testName "dual linear gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf (toDual r) (v :* u)) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (dualGrad $ linearF m)
>           (constF u (fmap unDual m))
> 
> 
> _test_dual_affine_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_dual_affine_gradient r =
>   testName "dual affine gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll2
>       (arbTensorOf (toDual r) (v :* u))
>       (arbTensorOf (toDual r) v) $
>       \m b ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (dualGrad $ affineF m b)
>           (constF u (fmap unDual m))
> 
> 
> _test_dual_pointwise_gradient_by
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => Metric -> String -> r -> (Dual r -> Dual r) -> (r -> r)
>   -> Test (Size -> Property)
> _test_dual_pointwise_gradient_by metric name r p q =
>   testName ("dual pointwise gradient (" ++ name ++ ")") $
>   \u -> u ~/= 0 ==> 
>     _test_functions_equal metric (10^^(-6))
>       (dualGrad $ pointwiseF u p)
>       (diagF u $. (pointwiseF u q))
> 
> 
> _test_dual_direct_sum_left_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_dual_direct_sum_left_gradient r =
>   testName "direct sum on left dual gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf r v) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (dualGrad $ dSumL u (fmap toDual m))
>           (constF u $ (zeros $ v :* u) ~-~ (idMat u))
> 
> 
> _test_dual_direct_sum_right_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, RealFloat r, Show r, Arbitrary r)
>   => r -> Test (Size -> Size -> Property)
> _test_dual_direct_sum_right_gradient r =
>   testName "direct sum on right dual gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll (arbTensorOf r v) $
>       \m ->
>         _test_functions_equal MaxAbsDiff (10^^(-5))
>           (dualGrad $ dSumR u (fmap toDual m))
>           (constF u $ (idMat u) ~-~ (zeros $ v :* u))


Test Suite
----------

> _test_gradient_checking
>   :: (Show r, Fractional r, RealFloat r, Ord r, Num r, Floating r, Arbitrary r)
>   => r -> Int -> Int -> IO ()
> _test_gradient_checking r num size = do
>   testLabel "Gradient"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   testLabel "Dual"
>   runTest args (_test_dual_scalar_gradient r)
>   runTest args (_test_dual_linear_gradient r)
>   runTest args (_test_dual_affine_gradient r)
>   runTest args (_test_dual_pointwise_gradient_by MaxAbsDiff
>                  "^2"  r (^2) (*2))
>   runTest args (_test_dual_pointwise_gradient_by MaxAbsDiff
>                  "sin" r sin cos)
>   runTest args (_test_dual_pointwise_gradient_by MaxAbsDiff
>                  "cos" r cos (negate . sin))
>   runTest args (_test_dual_pointwise_gradient_by MaxAbsDiff
>                  "exp" r exp exp)
>   runTest args (_test_dual_direct_sum_left_gradient r)
>   runTest args (_test_dual_direct_sum_right_gradient r)
> 
>   testLabel "Numerical"
>   runTest args (_test_numerical_scalar_gradient r)
>   runTest args (_test_numerical_linear_gradient r)
>   runTest args (_test_numerical_affine_gradient r)
>   runTest args (_test_numerical_pointwise_gradient_by MaxAbsDiff
>                  "^2"  r (^2) (*2))
>   runTest args (_test_numerical_pointwise_gradient_by MaxAbsDiff
>                  "sin" r sin cos)
>   runTest args (_test_numerical_pointwise_gradient_by MaxAbsDiff
>                  "cos" r cos (negate . sin))
>   runTest args (_test_numerical_pointwise_gradient_by MaxRelDiff
>                  "exp" r exp exp)
>   runTest args (_test_numerical_direct_sum_left_gradient r)
>   runTest args (_test_numerical_direct_sum_right_gradient r)
> 
> main_gradient_checking :: IO ()
> main_gradient_checking = _test_gradient_checking (0 :: Double) 100 3
