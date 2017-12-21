---
title: Equals
author: nbloomf
date: 2017-12-20
tags: literate-haskell, arithmetic-made-difficult
---

> module Equals where
> 
> import Booleans
> import NaturalNumbers
> import BailoutRecursion
> 
> import Test.QuickCheck

Equality
--------

We have an implicit equality among natural numbers, but in this post we'll make that relation computable. We won't say much else about this function.

<div class="result">
<div class="thm"><p>
Define $\beta : \nats \times \nats \rightarrow \bool$ by $$\beta(a,b) = \iszero(b),$$ $\psi : \nats \times \nats \rightarrow \bool$ by $$\psi(a,b) = \bfalse,$$ and $\omega : \nats \times \nats \rightarrow \nats$ by $$\omega(a,b) = \prev(b).$$ Now define $\nequal : \nats \times \nats \rightarrow \bool$ by $$\nequal = \bailrec{\iszero}{\beta}{\psi}{\omega}.$$

Then $$\nequal(a,b) = \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ a = b \\ \bfalse & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case, $a = \zero$, note that
$$\begin{eqnarray*}
 &   & \nequal(a,b) \\
 & = & \iszero(b) \\
 & = & \left\{ \begin{array}{ll} \btrue & \mathrm{if}\ b = a \\ \bfalse & \mathrm{otherwise} \end{array} \right.
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the result holds for some $a$. Now if $b = \zero$, we have $\nequal(\next(a),b) = \bfalse$, and indeed $\zero \neq \next(a)$. If $b \neq \zero$, then we have 
$$\begin{eqnarray*}
 &   & \nequal(\next(a),b) \\
 & = & \nequal(a,\prev(b)).
\end{eqnarray*}$$
And indeed, we have $$\next(a) = b$$ if and only if $$\prev(\next(a)) = \prev(b)$$ if and only if $$a = \prev(b)$$ as claimed.
</p></div>
</div>

In Haskell:

> instance (Natural t) => Equal (Nat t) where
>   eq = bailoutRec isZero beta psi omega
>     where
>       beta  _ b = isZero b
>       psi   _ _ = False
>       omega _ b = prev b

Note that we'll be writing functions against ``Nat t``, which is isomorphic to ``t``. This is so we can avoid undecidable instance declarations in Haskell.


Testing
-------

Let's give ``Natural`` a test drive. :) Here's a test of one simple property of equality.

> -- eq(a,a) == True
> _test_eq_reflexive :: (Natural n) => n -> Nat n -> Bool
> _test_eq_reflexive _ a =
>   eq (eq a a) True

And a test wrapper:

> -- run all tests for eq
> _test_eq :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_eq t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_eq_reflexive t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And a default main function:

> main_eq :: IO ()
> main_eq = _test_eq (zero :: Unary) 20 100
