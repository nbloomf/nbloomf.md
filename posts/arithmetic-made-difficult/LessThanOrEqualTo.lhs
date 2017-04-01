---
title: Less Than or Equal To
author: nbloomf
date: 2017-04-02
tags: arithmetic-made-difficult, literate-haskell
---

> module LessThanOrEqualTo
>  ( leq, _test_leq
>  ) where
> 
> import NaturalNumbers
> import Plus
> import Times
> 
> import Test.QuickCheck

Next we'd like to nail down what it means for one natural number to be less than or equal to another. Note that while $\nplus$ and $\ntimes$ have signatures $$\nats \times \nats \rightarrow \nats,$$ "less than or equal to" (which I will abbrebiate to *leq* from now on) does not. In fact $\leq$ is typically defined as a set of pairs. To make $\leq$ computable, we will instead (try to) define it as a function with signature $$\nats \times \nats \rightarrow \bool.$$ With this signature there is hope that we can define leq using primitive recursion, provided we can find appropriate maps $$\varphi : \nats \rightarrow \bool$$ and $$\mu : \nats \times \nats \times \bool \rightarrow \bool.$$ But what should $\varphi$ and $\mu$ be? Let's think about it.

One nice thing about $\primrec{\ast}{\ast}$ (and recursion operators in general) is that we can afford to be a little sloppy while looking for a good definition.

Let $\Theta = \primrec{\varphi}{\mu}$, and suppose $\Theta$ acts like the $\leq$ we know and love. Then for all $b$ we want, for instance, $$\btrue = \Theta(\zero,b) = \varphi(b);$$ evidently then we should have $\varphi(b) = \btrue$ for all $b$. Likewise, we have $$\Theta(\next(a),b) = \mu(a,b,\Theta(a,b)).$$ That is, the truth value of $a+1 \leq b$ is some function of $a$, $b$, and the truth value of $a \leq b$. Note that if $a = b$, then $a+1 \leq b$ is *false*. If $a > b$, then $a \leq b$ and $a+1 \leq b$ are both false, and if $a < b$, then $a \leq b$ and $a+1 \leq b$ are both true. So let's try $\mu(a,b,k) = \bfalse$ if $a = b$ and $k$ otherwise.

<div class="result">
<div class="defn"><p>
Let $\mu : \nats \times \nats \times \bool \rightarrow \bool$ be given by $$\mu(a,b,k) = \left\{ \begin{array}{ll} \bfalse & \mathrm{if}\ a = b \\ k & \mathrm{otherwise}, \end{array} \right.$$ and define $\varphi : \nats \rightarrow \bool$ by $\varphi(x) = \btrue$. We then define $\nleq : \nats \times \nats \rightarrow \bool$ by $$\nleq = \primrec{\varphi}{\mu}.$$
</p></div>
</div>

We can characterize $\nleq(a,b)$ in terms of the solubility of the equation $b = \nplus(a,x)$ as follows.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\nleq(a,b) = \btrue$ if and only if there exists a $c \in \nats$ such that $b = \nplus(a,c)$.
</div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``leq``:

> leq :: (Natural t) => t -> t -> Bool
> leq = primitiveRec phi mu
>   where
>     phi _ = True
>     mu a b k = if a == b then False else k

And some property tests:

> -- leq(a,a) == True
> _test_leq_reflexive :: (Natural t) => t -> t -> Bool
> _test_leq_reflexive _ a =
>   (leq a a) == True

And a test wrapper:

> -- run all tests for leq
> _test_leq :: (Natural t, Arbitrary t, Show t) => t -> Int -> IO ()
> _test_leq t numCases = sequence_
>   [ quickCheckWith args (_test_leq_reflexive t)
>   ]
>   where
>     args = stdArgs {maxSuccess = numCases}
