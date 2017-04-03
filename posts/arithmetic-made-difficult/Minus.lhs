---
title: Subtraction
author: nbloomf
date: 2017-04-05
tags: arithmetic-made-difficult, literate-haskell
---

> module Minus
>   ( minus, _test_minus
>   ) where
>
> import NaturalNumbers
> import Plus
> import Times
> import LessThanOrEqualTo
> 
> import Test.QuickCheck

Recall that $\nleq(a,b)$ is true if and only if the equation $b = \nplus(a,x)$ has a solution. Moreover, this solution (if it exists) is unique. When this happens in mathematics -- a thing exists and is unique -- it is frequently useful to give it a name. Putting on our third-grader hat of course the solution to $b = a+x$ is $x = b-a$. So we'll call this solution "b minus a". Our goal in this post is to give a constructive characterization for subtraction.

There's a hitch: whereas sums and products of natural numbers always exist, differences do not; $5 - 2 = 3$ is a natural number, but $5 - 7 = ???$ is not. So the signature of minus cannot be $\nats \times \nats \rightarrow \nats$. What is it then? How should we handle this?

I can think of three options. First, we can just declare that $b-a$ is not defined if the difference is not a natural number. The corresponding algorithm would then just error out. This should be avoided if possible.

The second option is to implement so-called *truncated subtraction*, so that anytime $b-a$ is not a natural number we simply call it 0. This also is not ideal, since now $b-a$ always exists, but the equation $b = a + (b-a)$ is no longer an identity and we cannot tell just from the value of $b-a$ whether it holds or not.

The third option is a blend of the first two. We can attach an extra element to $\nats$, say $\ast$, and then say $b-a = \ast$ if $b-a$ is not a natural number. This allows us to distinguish when $b-a$ does not exist but keeps the minus function total. So our signature for minus will be $$\nats \times \nats \rightarrow \ast + \nats$$

<div class="result">
<div class="defn"><p>
Define the map $\psi : (\ast + \nats)^\nats \rightarrow \ast + \nats$ by $$\psi(f) = \left\{ \begin{array}{ll} \ast & \mathrm{if}\ f(\zero) = \ast \\ \next(c) & \mathrm{if}\ f(\zero) = c \in \nats, \end{array} \right.$$ define $\mu : \nats \times (\ast + \nats)^\nats \times (\ast + \nats) \rightarrow \ast + \nats$ by $$\mu(x,f,y) = f(x),$$ and define $\Theta : (\ast + \nats)^\nats \times \nats \rightarrow \ast + \nats$ by $$\Theta(f,x) = \primrec{\psi}{\mu}(x)(f).$$

Now define $\varepsilon : \nats \rightarrow \ast + \nats$ by $$\varepsilon(a) = \left\{ \begin{array}{ll} \zero & \mathrm{if}\ a = \zero \\ \ast & \mathrm{otherwise}. \end{array} \right.$$

We then define $\nminus : \nats \times \nats \rightarrow \ast + \nats$ by $$\nminus(a,b) = \natrec{\varepsilon}{\Theta}(a)(b).$$
</p></div>
</div>

This definition looks complicated (primitive recursion nested inside natural recursion). Here's a useful lemma:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$. Then we have $$\nminus(\next(b),\next(a)) = \nminus(b,a).$$
</div>

<div class="proof"><p>
We have $$\begin{eqnarray*} & & \nminus(\next(b),\next(a)) \\ & = & \natrec{\varepsilon}{\Theta}(\next(b))(\next(a)) \\ & = & \Theta(\natrec{\varepsilon}{\Theta}(b))(\next(a)) \\ & = & \primrec{\psi}{\mu}(\next(a),\natrec{\varepsilon}{\Theta}(b)) \\ & = & \mu(a,\natrec{\varepsilon}{\Theta}(b),\primrec{\psi}{\mu}(a,\natrec{\varepsilon}{\Theta}(b))) \\ & = & \natrec{\varepsilon}{\Theta}(b)(a) \\ & = & \nminus(b,a) \end{eqnarray*}$$ as claimed.
</p></div>
</div>

And one more:

<div class="result">
<div class="lemma">
Let $a \in \nats$. Then we have $$\nminus(a,\zero) = a$$ and $$\nminus(\zero,\next(a)) = \ast.$$
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. For the base case, note that $$\nminus(\zero,\zero) = \natrec{\varepsilon}{\Theta}(\zero)(\zero) = \varepsilon(\zero) = \zero$$ as needed. For the inductive step, suppose the results holds for some $a \in \nats$. Now $$\begin{eqnarray*} & & \nminus(\next(a),\zero) \\ & = & \natrec{\varepsilon}{\Theta}(\next(a))(\zero) \\ & = & \Theta(\natrec{\varepsilon}{\Theta}(a))(\zero) \\ & = & \primrec{\psi}{\mu}(\zero)(\natrec{\varepsilon}{\Theta}(a)) \\ & = & \psi(\natrec{\varepsilon}{\mu}(a)) \\ & = & \next(a), \end{eqnarray*}$$ where in the last step we used the induction hypothesis since $$a = \nminus(a,\zero) = \natrec{\varepsilon}{\Theta}(a)(\zero).$$
2. Note that $$\begin{eqnarray*} & & \nminus(\zero,\next(a)) \\ & = & \natrec{\varepsilon}{\Theta}(\zero)(\next(a)) \\ & = & \varepsilon(\next(a)) \\ & = & \ast \end{eqnarray*}$$ since $\zero \neq \next(a)$.
</p></div>
</div>

We'd like to avoid having to reason about the guts of $\nminus$ as quickly as possible; to this end, we completely characterize $\nminus$ in terms of $\nleq$ with the next two results.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then the following are equivalent.

1. $\nleq(a,b) = \bfalse$.
2. $\nminus(b,a) = \ast$.
</div>

<div class="proof"><p>
First we show that (1) implies (2); we proceed by induction on $a$. For the base case $a = 0$, note that $\nleq(\zero,b)$ is true for all $b$, so the implication holds vacuously. For the induction step, suppose the implication holds for all $b$, for some $a$. Define $$B(x) = \{ b \in \nats \mid \mathrm{if}\ \nleq(a,b) = \bfalse\ \mathrm{then}\ \nminus(b,a) = \ast \}.$$ By the induction hypothesis we have $B(a) = \nats$, and we wish to show that $B(\next(a)) = \nats$. We do this by induction (again). For the base case $b = 0$, note that $\nleq(\next(a),\zero) = \bfalse$ and that $\nminus(\zero,\next(a)) = \ast$. For the inductive step, suppose the implication holds for some $b \in \nats$, and suppose further that $\nleq(\next(a),\next(b)) = \bfalse$. Now $\nleq(a,b)$ is also false, so that (by the second induction hypothesis) $\nminus(b,a) = \ast$, and hence $\nminus(\next(b),\next(a)) = \ast$ as needed.

Now we show that (2) implies (1); we proceed by induction on $b$. For the base case $b = 0$, suppose $\nminus(\zero,a) = \ast$. Now we must have $a \neq \zero$; say $a = \next(c)$. Then $\nleq(\next(c),\zero) = \bfalse$ as needed. For the inductive step, suppose the implication holds for all $a$ for some $b$. We show that it also holds for all $a$ for $\next(b)$ by induction on $a$. For the base case $a = \zero$, note that $\nminus(\next(b),\zero) = \next(b) \neq \ast$, so that the implication holds vacuously. For the inductive step, suppose the implication holds for $a \in \nats$. If $\nminus(\next(b),\next(a)) = \ast$, then we also have $\nminus(b,a) = \ast$. By the induction hypothesis, then $$\nleq(\next(a),\next(b)) = \nleq(a,b) = \bfalse$$ as needed.
</p></div>
</div>

And the second is like it:

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then the following are equivalent.

1. $\nminus(b,a) = c$.
2. $b = \nplus(a,c)$.
</div>

<div class="proof"><p>
First we show that (1) implies (2) by induction on $a$. For the base cse, note that $$\nplus(\zero,\nminus(b,\zero)) = \nminus(b,\zero) = b$$ for all $b$. For the inductive step, suppose the implication holds for all $b$ and $c$ for some $a$. We induct on $b$; in the base case ($b = \zero$) note that $\nminus(\zero,\next(a)) = \ast$, so that the implication holds vacuously. For the inductive step suppose the implication holds for all $c$ for some $b$. If $c = \nminus(b,a)$, then we have $$\begin{eqnarray*} & & \nplus(\next(a),\nminus(\next(b),\next(a))) \\ & = & \nplus(\next(a),\nminus(b,a)) \\ & = & \primrec{\id}{\mu_\nplus}(\next(a),\nminus(b,a)) \\ & = & \mu_\nplus(a,\nminus(b,a),\nplus(a,\nminus(b,a))) \\ & = & \mu_\nplus(a,\nminus(b,a),b) \\ & = & \next(b) \end{eqnarray*}$$ as needed.

Next we show that (2) implies (1), again by induction on $a$. For the base case $a = \zero$, note that if $b = \nplus(\zero,c) = c$, then we have $c = b = \nminus(b,\zero)$ as needed. For the inductive step, suppose the implication holds for all $b$ and $c$ for some $a$. Now we induct on $b$. For the base case $b = \zero$, note that $\zero = \nplus(\next(a),c)$ is false, so the implication holds vacuously. For the inductive step, suppose the implication holds for all $c$ for some $b$. Now suppose we have $$\nplus(\next(a),c) = \next(b);$$ then we have $\nplus(a,c) = b$, and using the induction hypothesis $$\nminus(\next(b),\next(a)) = \nminus(b,a) = c$$ as needed.
</p></div>
</div>

This result allows us to solve some "linear" equations (whatever that means).

<div class="result">
<div class="corollary">
Let $a,b \in \nats$. Then the equation $\nplus(a,x) = b$ has a unique solution $x = \nminus(b,a)$ if $\nleq(b,a) = \btrue$, and no solution otherwise.
</div>
</div>


Implementation and Testing
--------------------------

Here's ``minus``:

> minus :: (Natural t) => t -> t -> Maybe t
> minus = naturalRec eps theta
>   where
>     eps k = if k == zero then Just zero else Nothing
> 
>     theta f x = (primitiveRec psi mu) x f
>       where
>         psi f = fmap next (f zero)
>         mu x f _ = f x

And some properties:

> _test_minus_next :: (Natural t) => t -> t -> t -> Bool
> _test_minus_next _ a b =
>   (minus (next a) (next b)) == (minus a b)
> 
> 
> _test_minus_zero_left :: (Natural t) => t -> t -> Bool
> _test_minus_zero_left _ a =
>   (minus zero (next a)) == Nothing
> 
> 
> _test_minus_zero_right :: (Natural t) => t -> t -> Bool
> _test_minus_zero_right _ a =
>   (minus a zero) == Just a
> 
> 
> _test_minus_leq :: (Natural t) => t -> t -> t -> Bool
> _test_minus_leq _ a b =
>   ((leq a b) == False) == ((minus b a) == Nothing)

And a suite:

> _test_minus :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_minus t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_minus_next t)
>   , quickCheckWith args (_test_minus_zero_left t)
>   , quickCheckWith args (_test_minus_zero_right t)
>   , quickCheckWith args (_test_minus_leq t)
>   ]
>   where
>     args = stdArgs
>      { maxSuccess = numCases
>      , maxSize    = maxSize
>      }
