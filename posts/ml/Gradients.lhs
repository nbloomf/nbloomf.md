---
title: Gradients
author: nbloomf
date: 2017-10-15
tags: ml, literate-haskell
---

> module Gradients where
> 
> import Control.Applicative
> import Test.QuickCheck
> import Test.QuickCheck.Test
> 
> import Indices
> import IndexIsos
> import Tensors

Later on we'll need to do some calculus on tensor functions. Since this is not really specific to learning, I'll put some notes on this here.


Tensor Functions
----------------

Ostensibly a "tensor function" is just a function with signature ``Tensor r -> Tensor r``. But it turns out this is not quite right. Tensor functions should be well defined on size -- a function should expect as input functions of some uniform size $u$ and should produce tensors of some other uniform size $v$. As we've implemented tensors here, plain haskell functions can't enforce this, so we'll abstract functions behind a type that can.

> data Function r = F
>   { dom :: Size
>   , cod :: Size
>   , fun :: Tensor r -> Tensor r
>   }
> 
> -- apply
> ($@) :: Function r -> Tensor r -> Tensor r
> f $@ v = if (size v) /= dom f
>   then error "($@): domain mismatch"
>   else let w = (fun f) v in
>     if (size w) /= cod f
>       then error "($@): codomain mismatch"
>       else w
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
>     else error "($.): domain/codomain mismatch"

We can also build a small library of functions in this style.

> -- constant function
> constF :: (Num r) => Size -> Tensor r -> Function r
> constF u a = F
>   { dom = u
>   , cod = size a
>   , fun = \_ -> a
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
> -- "matrix"-"vector" multiplication
> linearF :: (Num r) => Tensor r -> Function r
> linearF m@(T (v :* u) _) = F
>   { dom = u
>   , cod = v
>   , fun = \w -> m `collapse` w
>   }
> 
> -- "matrix"-"vector" multiplication plus a constant
> affineF :: (Num r) => Tensor r -> Tensor r -> Function r
> affineF m@(T (v :* u) _) b@(T w _) =
>   if v == w
>     then F
>       { dom = u
>       , cod = v
>       , fun = \z -> (m `collapse` z) .+ b
>       }
>     else error "affineF: dimension mismatch"
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


Gradients
---------

First some review on derivatives. If $f : \mathbb{R} \rightarrow \mathbb{R}$ is a function, then the <em>derivative</em> of $f$ at $x \in \mathbb{R}$, denoted $(Df)(x)$, is given by $$(Df)(x) = \lim_{h \rightarrow 0} \frac{f(x+h) - f(x)}{h},$$ if the limit exists. In this case we say $f$ is <em>differentiable</em> at $x \in \mathbb{R}$. We can think of $Df$ as a function $\mathbb{R} \rightarrow \mathbb{R}$. In a concrete sense, $(Df)(x)$ is the slope of the best linear approximation to $f$ at $x$.

This notion of "best linear approximation" is a useful one, so a natural question is how to generalize it to other kinds of functions. In particular, to functions that take more than one input and produce more than one output; say with signature $\mathbb{R}^m \rightarrow \mathbb{R}^n$. This is a little more complicated. First off, note that we don't really need to consider functions with more than one output, since any such function can be constructed out of one-output functions using the universal property of cartesian products. In concrete terms, a function $f : \mathbb{R}^2 \rightarrow \mathbb{R}^2$ like $$f(x,y) = (2x+y, x-3y)$$ is induced by the "coordinate functions" $f_1(x,y) = 2x+y$ and $f_2(x,y) = x-3y$. So we're really interested in finding a "derivative" for functions like $f : \mathbb{R}^m \rightarrow \mathbb{R}$.

We already know how to take derivatives of functions with one input, so one idea is to shoehorn $f$ into taking only one input, and differentiating that. Say $v \in \mathbb{R}^m$ is the point where we want the derivative, and choose some index $k \in m$. We now define a map $w_{k,v} : \mathbb{R} \rightarrow \mathbb{R}^m$ piecewise like so: $$w_{k,v}(x)_i = \left\{ \begin{array}{ll} v_i & \mathrm{if}\ i \neq k \\ x & \mathrm{if}\ i = k. \end{array} \right.$$ That is, $w_{k,v}(x)$ is $x$ in the $k$th coordinate, and agrees with $v$ everywhere else. Now $f \circ w_{k,v}$ is a map $\mathbb{R} \rightarrow \mathbb{R}$, so we can take its derivative in the usual way. This is called the $k$th <em>partial derivative</em> of $f$ at $v$, and sometimes denoted $(\frac{\partial}{\partial x_k}f)(v)$. That is, we define $$\left(\frac{\partial}{\partial x_k}f\right)(v) = D(f(w_{k,v}(x)))(v).$$

The full "derivative" of a multivariate function, called the <em>gradient</em>, is the tensor of partial derivatives at each coordinate. This tensor is also called the Jacobian.

More precisely: the gradient of a tensor function $f : \mathbb{R}^A \rightarrow \mathbb{R}^B$ at a point $v \in \mathbb{R}^A$, denoted $(\nabla f)(v)$, is a tensor in $\mathbb{R}^{B \otimes A}$, whose entry at $b \& a \in B \otimes A$ is given by $$(\nabla f)(v)_{b \& a} = D(f(w_{a,v}(x))_b)(v_a).$$ We can think of $\nabla f$ as a mapping with signature $$\mathbb{R}^A \rightarrow \mathbb{R}^{B \otimes A}.$$ Like the univariate derivative, the gradient also represents a "best linear approximation" at a point, although "line" now means "$n$-dimensional hyperplane" and everything is hard to visualize.

This definition for gradient is scary at first, but take heart: it means that finding the derivative of a hairy multivariate function requires nothing more than (1) computing plain old univariate derivatives and (2) maybe some intricate case analysis on tensor indices. Those things are tedious, but not super difficult. This is good news. :)


Example: "Linear" Functions
---------------------------

As an example, let's compute a concrete gradient. Let $H$ and $K$ be tensor sizes, and say we have tensors $M \in \mathbb{R}^{K \otimes H}$ and $B \in \mathbb{R}^K$. We can define a tensor function $f : \mathbb{R}^H \rightarrow \mathbb{R}^K$ by $$f(V) = MV + B,$$ where $MV$ denotes "matrix"-"vector" multiplication and $+$ is pointwise addition. Then $\nabla f$ is a function with signature $\mathbb{R}^H \rightarrow \mathbb{R}^{K \otimes H}$. Given some $V \in \mathbb{R}^H$ and $k \& h \in K \otimes H$, the $k \& h$ entry of the gradient of $f$ at $V$ is

$$\begin{eqnarray*}
 &   & (\nabla f)(V)_{k \& h} \\
 & = & D(f(w_{h,V}(x))_k)(V_h) \\
 & = & D((Mw_{h,V}(x) + B)_k)(V_h) \\
 & = & D((Mw_{h,V}(x))_k + B_k)(V_h) \\
 & = & D\left(\sum_{i \in H} M_{k \& i} w_{h,V}(x)_i + B_k\right)(V_h) \\
 & = & D\left(M_{k \& h}w_{h,V}(x)_h + \sum_{i \in H, i \neq h} M_{k \& i} w_{h,V}(x)_i + B_k\right)(V_h) \\
 & = & D\left(M_{k \& h}x + \sum_{i \in H, i \neq h} M_{k \& i}V_i + B_k\right)(V_h) \\
 & = & D(M_{k \& h}x)(V_h) \\
 & = & \overline{M_{k \& h}}(V_h) \\
 & = & M_{k \& h}
\end{eqnarray*}$$

In the fourth to last line we use the fact that the derivative is additive, and the derivative of a constant function is zero. In the second to last line, we use $\overline{\alpha}$ to denote the constant function returning $\alpha$.

That is:

<div class="result">
<div class="thm">
Fix $M \in \mathbb{R}^{K \otimes H}$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^H \rightarrow \mathbb{R}^K$ by $f(X) = MX + B$. Then $$\nabla f : \mathbb{R}^{H} \rightarrow \mathbb{R}^{K \otimes H}$$ is given by $$(\nabla f)(X) = M.$$
</div>
</div>

So $\nabla f$ is a constant function, always returning $M$.

We can also think of $MX+B$ as a function of $M$. That is, fix $V \in \mathbb{R}^H$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^K$ by $$f(M) = MV + B.$$ Now $$\nabla f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^{K \otimes (K \otimes H)}.$$ If $t\&(k\&h) \in K \otimes (K \otimes H)$, we have two possibilities, depending on whether $t = k$ or not. If $t \neq k$, we have

$$\begin{eqnarray*}
 &   & (\nabla f)(M)_{t\&(k\&h)} \\
 & = & D(f(w_{k\&h,M}(x))_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V + B)_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V)_t + B_t)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} M_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & \overline{0}(M_{k\&h}) \\
 & = & 0,
\end{eqnarray*}$$

and if $t = k$ we have

$$\begin{eqnarray*}
 &   & (\nabla f)(M)_{t\&(k\&h)} \\
 & = & D(f(w_{k\&h,M}(x))_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V + B)_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V)_t + B_t)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(w_{k\&h,M}(x)_{t\&h}V_h + \sum_{i \in H, i \neq h} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(xV_h + \sum_{i \in H, i \neq h} M_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D(xV_h)(M_{k\&h}) \\
 & = & \overline{V_h}(M_{k\&h}) \\
 & = & V_h.
\end{eqnarray*}$$

That is:

<div class="result">
<div class="thm">
Fix $V \in \mathbb{R}^H$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^K$ by $f(M) = MV + B$. Then $$\nabla f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^{K \otimes (K \otimes H)}$$ is given by  $$(\nabla f)(M)_{t\&(k\&h)} = \left\{\begin{array}{ll} V_h & \mathrm{if}\ t = k \\ 0 & \mathrm{otherwise}. \end{array}\right.$$
</div>
</div>


Linearity and the Chain Rule
----------------------------

The gradient defined above is computationally useful, but not theoretically enlightening. It turns out that the usual definition of derivative for univariate functions generalizes nicely to general multivariate functions. The search term here is [Fréchet derivative](https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative). There is an alternative characterization of derivatives, due to Carathéodory, that makes the proofs of linearity and the chain rule for derivatives really clear, and this characterization also generalizes really nicely. I'm not super interested in retyping those proofs here, so I'll just link to the paper [Fréchet vs. Carathéodory](http://www.docentes.unal.edu.co/eacostag/docs/FreCarat_Acosta.pdf), by Acosta and Delgado, where I saw them.

The point is that as a function, gradient is linear in the sense that $$\nabla(\alpha f + \beta g) = \alpha (\nabla f) + \beta (\nabla g)$$ for tensor functions $f$ and $g$ and real numbers $\alpha$ and $\beta$ so long as the signatures make sense.

Moreover we have a multivariate chain rule. If $f$ and $g$ are tensor functions and $g \circ f$ makes sense, then $$\nabla(g \circ f)(V) = \nabla(g)(f(V)) \cdot \nabla(f)(V),$$ where the $\cdot$ denotes tensor contraction (a.k.a. matrix multiplication). The proof of this is complicated and technical if we use Fréchet's definition of the derivative and is <em>almost</em> trivial if we use Carathéodory's definition. I'll refer to the paper for details, but we can at least check that the types make sense. Say $f : \mathbb{R}^A \rightarrow \mathbb{R}^B$ and $g : \mathbb{R}^B \rightarrow \mathbb{R}^C$. Then $\nabla g : \mathbb{B} \rightarrow \mathbb{R}^{C \otimes B}$ and $\nabla f : \mathbb{R}^A \rightarrow \mathbb{R}^{B \otimes A}$. If $V \in \mathbb{R}^A$, then $f(V) \in \mathbb{R}^B$, and $(\nabla g)(f(V)) \in \mathbb{R}^{C \otimes B}$. We also have $\nabla(f)(V) \in \mathbb{R}^{B \otimes A}$, and the final contraction gives $$\nabla(g)(f(V)) \cdot \nabla(f)(V) \in \mathbb{R}^{C \otimes A}$$ as expected.

The chain rule is especially nice. It means that to evaluate the gradient of $g \circ f$ at a tensor $V$, all we need to know is (1) the value of $f$ at $V$, (2) the gradient of $g$ at $f(V)$, and (3) the gradient of $f$ at $V$. We will use this later in a big way.


Gradient Checking: Numerical Approximation
------------------------------------------

Computing gradients of multivariate $f$ is intricate, so it'd be nice to have a simple (if slow) way to check them for reasonableness. In the single variable case the gradient at a point $v$ is the slope of the line tangent to $f$ at $v$, which can be approximated using the slope of the secant line passing through the points on $f$ at $v \pm \varepsilon$ for small epsilon, sometimes called the <em>difference quotient</em>.

> diffquo :: (Num r, Fractional r) => (r -> r) -> r -> r -> r
> diffquo f x eps = ((f $ x + eps) - (f $ x - eps)) / (2*eps)

Of course the gradient is a bunch of pointwise univariate derivatives, so we can approximate the gradient pointwise. Note that we have to keep track of the input and output sizes for our function.

> gradApprox
>   :: (Num r, Fractional r)
>   => Function r -- function to approximate
>   -> Tensor r   -- point to approximate at
>   -> r          -- pointwise epsilon
>   -> Tensor r   -- approximate gradient
> 
> gradApprox f v eps =
>   let
>     g i j x = (f $@ (inj i v x))`at`j
>   in
>     tensor ((cod f) :* (dom f)) $
>       \(j :& i) -> diffquo (g i j) (v`at`i) eps
> 
>   where
>     inj :: Index -> Tensor r -> r -> Tensor r
>     inj k a@(T u _) x = tensor u $
>       \i -> if i == k then x else a`at`i

So ``gradApprox`` computes the numerical gradient at a point using some tolerance ``epsilon``. If we have some other function that claims to compute the gradient, a decent reasonableness check is to see whether the numerical gradient at $v$ and the "exact" gradient at $v$ are equal, or, more likely, very close to each other. "Very close" for tensors can be measured in a few ways, each appropriate in different cases. ``maxAbsDiff`` finds the maximum pointwise absolute difference, and ``maxRelDiff`` finds the maximum pointwise relative difference.

> data MetricType
>   = MaxAbsDiff -- absolute difference
>   | MaxRelDiff -- relative difference
>   deriving (Eq, Show)

> metric
>   :: (Num r, Ord r, Fractional r)
>   => MetricType -> Tensor r -> Tensor r -> r
> metric m a b = case m of
>   MaxAbsDiff -> maximum $ tzipWith f a b
>     where f x y = abs (x - y)
>   MaxRelDiff -> maximum $ tzipWith f a b
>     where f x y = abs $ (x - y) / (max x y)

> maxAbsDiff :: (Num r, Ord r, Fractional r) => Tensor r -> Tensor r -> r
> maxAbsDiff a b = maximum $ tzipWith f a b
>   where
>     f x y = abs (x - y)

> maxRelDiff :: (Num r, Ord r, Fractional r) => Tensor r -> Tensor r -> r
> maxRelDiff a b = maximum $ tzipWith f a b
>   where
>     f x y = abs $ (x - y) / (max x y)

Then ``checkGradient`` (in absolute and relative flavors) is straightforward enough.

> checkGradientAbs, checkGradientRel
>   :: (Num r, Ord r, Fractional r)
>   => MetricType -- how to measure closeness
>   -> Function r -- function to approximate
>   -> Function r -- "exact" gradient
>   -> Tensor r   -- point to compare at
>   -> r          -- tolerance for approximation
>   -> r          -- pointwise tolerance
>   -> Bool
> 
> checkGradientAbs f gradF v del eps =
>   (maxAbsDiff (gradApprox f v del) (gradF $@ v)) < eps
> 
> checkGradientRel f gradF v del eps =
>   (maxRelDiff (gradApprox f v del) (gradF $@ v)) < eps

For example, the gradient of scalar multiplication should be a scalar multiple of the "identity" tensor; the following test verifies this.

> _test_numerical_scalar_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, Show r, Arbitrary r)
>   => r
>   -> Test (Size -> Property)
> _test_numerical_scalar_gradient r =
>   testName "numerical scalar gradient" $
>   \u -> u ~/= 0 ==> 
>     forAll (arbTensor u) $
>       \v k ->
>         let
>           () = k `withTypeOf` r
> 
>           func = scalarF u k
>           grad = constF u (k .@ (idMat u))
>         in
>           checkGradientAbs func grad v (10^^(-6)) (10^^(-6))

More generally, the gradient of a "linear" tensor function is a constant.

> _test_numerical_linear_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Show r, Arbitrary r)
>   => r
>   -> Test (Size -> Size -> Property)
> _test_numerical_linear_gradient r =
>   testName "numerical linear gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll2 (arbTensor (v :* u)) (arbTensor u) $
>       \m z ->
>         let
>           () = z `withTypeOf` (cell r)
> 
>           func = linearF m
>           grad = constF u m
>         in
>           checkGradientAbs func grad z (10^^(-5)) (10^^(-5))

Yet more generally still, the gradient of an "affine" tensor function is a constant.

> _test_numerical_affine_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Show r, Arbitrary r)
>   => r
>   -> Test (Size -> Size -> Property)
> _test_numerical_affine_gradient r =
>   testName "numerical affine gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll3 (arbTensor (v :* u)) (arbTensor v) (arbTensor u) $
>       \m b z ->
>         let
>           () = z `withTypeOf` (cell r)
> 
>           func = affineF m b
>           grad = constF u m
>         in
>           checkGradientAbs func grad z (10^^(-5)) (10^^(-5))

Pointwise functions (in both absolute and relative flavors):

> _test_pointwise_gradient_abs
>   :: (Eq r, Num r, Ord r, Fractional r, Show r, Arbitrary r)
>   => String
>   -> r
>   -> (r -> r)
>   -> (r -> r)
>   -> Test (Size -> Property)
> _test_pointwise_gradient_abs str r p q =
>   testName ("pointwise gradient (" ++ str ++ ")") $
>   \u -> u ~/= 0 ==> 
>     forAll (arbTensor u) $
>       \v ->
>         let
>           func = pointwiseF u p
>           grad = diagF u $. (pointwiseF u q)
>         in
>           checkGradientAbs func grad v (10^^(-4)) (10^^(-4))
> 
> _test_pointwise_gradient_rel
>   :: (Eq r, Num r, Ord r, Fractional r, Show r, Arbitrary r)
>   => String
>   -> r
>   -> (r -> r)
>   -> (r -> r)
>   -> Test (Size -> Property)
> _test_pointwise_gradient_rel str r p q =
>   testName ("pointwise gradient (" ++ str ++ ")") $
>   \u -> u ~/= 0 ==> 
>     forAll (arbTensor u) $
>       \v ->
>         let
>           func = pointwiseF u p
>           grad = diagF u $. (pointwiseF u q)
>         in
>           checkGradientRel func grad v (10^^(-2)) (10^^(-2))


Gradient Checking: Dual Numbers
-------------------------------

Another neat trick for computing the gradient of a function is automatic differentiation using <em>dual numbers</em>. For the single variable case, this method works by embedding $\mathbb{R}$ in the ring $\mathbb{R}[x]/(x^2)$. Given $a + bx$ in this ring, $a$ is called the <em>real part</em> and $b$ the <em>infinitesimal part</em>. Carrying out arithmetic as usual makes $b$ act like the derivative of $a$. I won't go into the details, mostly because they're a little bit magic to me still, but this can be extended to the multivariate case, as we'll do.

Remember that the gradient of a tensor function is again a tensor. So rather than keeping track of a number and its derivative, we'll keep track of a number and its gradient tensor.

> data Dual r
>   = D r (Tensor r)
>   deriving (Eq, Show)
> 
> toDual :: r -> Dual r
> toDual x = D x empty
> 
> unDual :: Dual r -> r
> unDual (D x _) = x

Thinking of a tensor as a "variable", we dualize by embedding each corrdinate with its partial derivative.

> dualize :: (Num r) => Tensor r -> Tensor (Dual r)
> dualize a@(T u _) = tensor u (\i -> var u i (a`at`i))
>   where
>     var :: (Num r) => Size -> Index -> r -> Dual r
>     var u k r = D r (tensor u (\i -> if i == k then 1 else 0))

Now we define arithmetic on dual numbers, in a way that essentially encodes the chain rule at each step.

> instance Scalable Dual where
>   r .@ (D x dx) = D (r*x) (fmap (r*) dx)
> 
> 
> instance (Eq r, Num r) => Num (Dual r) where
>   fromInteger x = toDual (fromInteger x)
> 
>   (D x dx) + (D y dy)
>     | dx == empty = D (x + y) dy
>     | dy == empty = D (x + y) dx
>     | otherwise   = D (x + y) (dx .+ dy)
> 
>   (D x dx) * (D y dy)
>     | dx == empty = x .@ (D y dy)
>     | dy == empty = y .@ (D x dx)
>     | otherwise = D (x * y) ((y .@ dx) .+ (x .@ dy))
> 
>   negate (D x dx) = D (negate x) (fmap negate dx)
> 
>   abs (D x dx) = D (abs x) ((signum x) .@ dx)
> 
>   signum (D x dx) = D (signum x) (0 .@ dx)
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
>   (D x dx) ** (D y dy) = D (x**y)
>     ((x**y) .@ (((log x) .@ dy) .+ ((y/x) .@ dx)))
>   logBase (D x dx) (D y dy) = D (logBase x y)
>     ((1/(log x)**2) .@ ((((log y)/x) .@ dy) .- (((log x)/y) .@ dy)))

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

As a quick hand test:

```haskell
$> let f = pointwiseF 1 sin
$> let g = dualGrad f -- magic
$> g $@ (cell pi)
-1.0
$> let f = pointwiseF 3 (^2)
$> let g = dualGrad f -- magic
$> g $@ (vec [1,2,3])
2 0 0
0 4 0
0 0 6
```

I will probably never get used to that. Anyway, like we did with numeric differentiation, we can use automatic differentiation to test a claimed "exact" gradient. By the way -- AD gives us the exact gradient, so why don't we just use it? Unfortunately AD ends up doing a lot of work to keep track of those intermediate derivatives, so a dedicated gradient function (if we can find it) can be more efficient. But we can still test our handwritten gradients against the AD gradient or numeric gradient on small functions to gain confidence that we're doing it right.

> checkDualGradientAbs, checkDualGradientRel
>   :: (Num r, Ord r, Fractional r)
>   => Function (Dual r) -- function to approximate
>   -> Function r        -- "exact" gradient
>   -> Tensor r          -- point to compare at
>   -> r                 -- pointwise tolerance
>   -> Bool
> 
> checkDualGradientAbs f g v eps =
>   let
>     h = (dualGrad f) $@ v
>     k = g $@ v
>   in
>     (maxAbsDiff h k) < eps
> 
> checkDualGradientRel f g v eps =
>   let
>     h = (dualGrad f) $@ v
>     k = g $@ v
>   in
>     (maxRelDiff h k) < eps

> _test_dual_scalar_gradient
>   :: (Eq r, Num r, Ord r, Fractional r, Show r, Arbitrary r)
>   => Dual r
>   -> Test (Size -> Property)
> _test_dual_scalar_gradient r =
>   testName "dual scalar gradient" $
>   \u -> u ~/= 0 ==> 
>     forAll (arbTensor u) $
>       \v k ->
>         let
>           () = k `withTypeOf` r
> 
>           func = scalarF u k
>           grad = constF u ((unDual k) .@ (idMat u))
>         in
>           checkDualGradientAbs func grad v (10^^(-6))

> _test_dual_linear_gradient
>   :: (Eq r, Ord r, Num r, Fractional r, Show r, Arbitrary r)
>   => Dual r
>   -> Test (Size -> Size -> Property)
> _test_dual_linear_gradient r =
>   testName "dual linear gradient" $
>   \u v -> (u ~/= 0) && (v ~/= 0) ==>
>     forAll2 (arbTensor (v :* u)) (arbTensor u) $
>       \m z ->
>         let
>           () = m `withTypeOf` (cell r)
>           func = linearF m
>           grad = constF u (fmap unDual m)
>         in
>           checkDualGradientAbs func grad z (10^^(-5))

> instance (Arbitrary r) => Arbitrary (Dual r) where
>   arbitrary = do
>     x <- arbitrary
>     return $ D x empty

> arbDualTensor :: (Num r, Arbitrary r) => Size -> Gen (Tensor (Dual r))
> arbDualTensor u = do
>   m <- arbTensor u
>   return $ dualize m


Test Suite
----------

> _test_gradients :: (Show r, Fractional r, Ord r, Num r, Floating r, Arbitrary r)
>   => r -> Int -> Int -> IO ()
> _test_gradients r num size = do
>   testLabel "Gradient"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_numerical_scalar_gradient r)
>   runTest args (_test_numerical_linear_gradient r)
>   runTest args (_test_numerical_affine_gradient r)
>   runTest args (_test_pointwise_gradient_abs "^2"  r (^2) (*2))
>   runTest args (_test_pointwise_gradient_abs "sin" r sin cos)
>   runTest args (_test_pointwise_gradient_abs "cos" r cos (negate . sin))
>   runTest args (_test_pointwise_gradient_rel "exp" r exp exp)
> 
>   runTest args (_test_dual_scalar_gradient (toDual r))
>   runTest args (_test_dual_linear_gradient (toDual r))
> 
> main_gradients :: IO ()
> main_gradients = _test_gradients (0 :: Double) 100 3
