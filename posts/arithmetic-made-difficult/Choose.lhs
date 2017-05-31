---
title: Choose
author: nbloomf
date: 2017-04-15
tags: arithmetic-made-difficult, literate-haskell
---

> module Choose
>   ( choose, _test_choose, main_choose
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import Divides
> 
> import Prelude ()
> import Test.QuickCheck

Today we'll define the binomial coefficient operator, $\nchoose$.

<div class="result">
<div class="defn"><p>
Define mappings $\varphi : \nats \times \nats \rightarrow \nats$ by $$\varphi(a,b) = \bif{\iszero(a)}{\next(\zero)}{\zero},$$ $\omega : \nats \times \nats \rightarrow \nats \times \nats$ by $$\omega(a,b) = (\prev(a),a),$$ and $\chi : \nats \times \nats \rightarrow \nats^{\nats \times \nats} \rightarrow \nats$ by $$\chi((a,b),f) = \bif{\iszero(b)}{\next(\zero)}{\nplus(f(b),f(a))}.$$ We then define $\nchoose : \nats \times \nats \rightarrow \nats$ by $$\nchoose = \mutrec{\varphi}{\omega}{\chi}.$$
</p></div>
</div>

We can implement $\nchoose$ using the definition:

> choose' :: (Natural n) => n -> n -> n
> choose' = mutatingRec phi omega chi
>   where
>     phi a _ = if isZero a then next zero else zero
>     omega (a,_) = (prev a, a)
>     chi (a,b) f = if isZero b then next zero else plus (f b) (f a)

The following theorem suggests a more straightforward implementation.

<div class="result">
<div class="thm">
We have the following.

1. $\nchoose(\zero,k) = \bif{\isZero(k)}{\}{}.$
</div>

<div class="proof"><p>

</p></div>
</div>



<div class="result">
<div class="thm">

</div>

<div class="proof"><p>

</p></div>
</div>


Implementation and Testing
--------------------------

Property tests:

> -- power(a,0) == 1
> _test_choose_zero_left :: (Natural n)
>   => n -> Nat n -> Bool
> _test_choose_zero_left _ a =
>   if isZero a
>     then (choose zero a) == zero
>     else (choose zero a) == (next zero)

And the suite:

> -- run all tests for choose
> _test_choose ::
>   ( TypeName n, Natural n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_choose n maxSize numCases = do
>   testLabel ("choose: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_choose_zero_left n)

And the main function:

> main_choose :: IO ()
> main_choose = do
>   _test_choose (zero :: Unary) 4 30
