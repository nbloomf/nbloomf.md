---
title: Subtraction
author: nbloomf
date: 2017-04-02
tags: arithmetic-made-difficult, literate-haskell
---

> module Minus
>   ( minus, _test_minus, main_minus
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> 
> import Prelude ()
> import Test.QuickCheck

We'd eventually like to solve some equations; for instance, one of the simplest equations we can construct with the tools we have so far is $$\nplus(a,x) = b$$ where $a$ and $b$ are in $\nats$. Putting on our third-grader hat of course the solution to $b = a+x$ is $x = b-a$. So we'll call this solution "b minus a". Our goal in this post is to give a constructive characterization for subtraction.

There's a hitch: whereas sums and products of natural numbers always exist, differences do not; $5 - 2 = 3$ is a natural number, but $5 - 7 = ?$ is not. So the signature of minus cannot be $\nats \times \nats \rightarrow \nats$. What is it then? How should we handle this?

I can think of three options. First, we can just declare that $b-a$ is not defined if the difference is not a natural number. The corresponding algorithm would then just error out. This should be avoided if possible.

The second option is to implement so-called *truncated subtraction*, so that anytime $b-a$ is not a natural number we simply call it 0. This also is not ideal, since now $b-a$ always exists, but the equation $b = a + (b-a)$ is no longer an identity and we cannot tell just from the value of $b-a$ whether it holds or not.

The third option is a blend of the first two. We can attach an extra element to $\nats$, say $\ast$, and then say $b-a = \ast$ if $b-a$ is not a natural number. This allows us to distinguish when $b-a$ does not exist but keeps the minus function total. So our signature for minus will be $$\nats \times \nats \rightarrow \ast + \nats$$

<div class="result">
<div class="defn"><p>
Define maps $\varphi : \nats \rightarrow \ast + \nats$ by $$\varphi(x) = \left\{\begin{array}{ll} \zero & \mathrm{if}\ x == \zero \\ \ast & \mathrm{otherwise}; \end{array}\right.$$ $\beta : \nats \times \nats \rightarrow \bool$ by $$\beta(a,b) = \left\{\begin{array}{ll} \btrue & \mathrm{if}\ b = \zero \\ \bfalse & \mathrm{otherwise}; \end{array}\right.$$ $\psi : \nats \times \nats \rightarrow \ast + \nats$ by $$\psi(a,b) = \next(a);$$ and $\omega : \nats \times \nats \rightarrow \nats$ by $$\omega(a,b) = \prev(b).$$

Now define $\nminus : \nats \times \nats \rightarrow \ast + \nats$ by $$\nminus = \bailrec{\varphi}{\beta}{\psi}{\omega}.$$

In Haskell:

> minus :: (Natural t) => t -> t -> Maybe t
> minus = bailoutRec phi beta psi omega
>   where
>     phi x = if isZero x
>       then Just zero
>       else Nothing
> 
>     beta _ b = isZero b
> 
>     psi a _ = Just (next a)
> 
>     omega _ b = prev b

</p></div>
</div>

This is our first time using bailout recursion. Woo! As a reminder, $\nminus$ satisfies the following:
$$\begin{eqnarray*}
\nminus(\zero,a) & = & \left\{\begin{array}{ll} \zero & \mathrm{if}\ a = \zero \\ \ast & \mathrm{otherwise} \end{array}\right. \\
 & & \\
\nminus(\next(b),a) & = & \left\{\begin{array}{ll} \next(b) & \mathrm{if}\ a = \zero \\ \nminus(b,\prev(a)) & \mathrm{otherwise}. \end{array}\right.
\end{eqnarray*}$$

Here are some special cases:

<div class="result">
<div class="lemma">
Let $a \in \nats$. Then we have $$\nminus(a,\zero) = a$$ and $$\nminus(\zero,\next(a)) = \ast.$$
</div>

<div class="proof"><p>
1. If $a = \zero$, then $$\nminus(\zero,\zero) = \varphi(\zero) = \zero.$$ If $a = \next(b)$, then we have $$\nminus(\next(b),\zero) = \psi(b,\zero) = \next(b) = a$$ as needed.
2. We have $$\nminus(\zero,\next(a)) = \psi(\next(a)) = \ast$$ as claimed.
</p></div>
</div>

And a useful lemma:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$. Then we have $$\nminus(\next(b),\next(a)) = \nminus(b,a).$$
</div>

<div class="proof"><p>
Note that $\next(b) \neq \zero$, so we have
$$\begin{eqnarray*}
 &   & \nminus(\next(b),\next(a)) \\
 & = & \nminus(b,\prev(\next(a))) \\
 & = & \nminus(b,a)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The next result shows that $\nminus$ gives a solution to the equation $b = \nplus(a,x)$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then the following are equivalent.

1. $\nminus(b,a) = c$.
2. $b = \nplus(a,c)$.
</div>

<div class="proof"><p>
First we show (1) implies (2) by induction on $b$. For the base case, suppose we have $\nminus(\zero,a) = c$. Now $$c = \nminus(\zero,a) = \varphi(a),$$ so that $a = \zero$ and $c = \zero$. Then $\zero = \nminus(a,c)$ as claimed. For the inductive step, suppose the result holds for some $b$, and suppose further that $\nminus(\next(b),a) = c$. If $a = \zero$, we have $$c = \nminus(\next(b),\zero) = \psi(b,\zero) = \next(b),$$ so that $\next(b) = \nplus(c,\zero)$ as needed. If $a \neq \zero$, then we have $a = \next(d)$ for some $d$. Now
$$\begin{eqnarray*}
 &   & c \\
 & = & \nminus(\next(b),a) \\
 & = & \nminus(\next(b),\next(d)) \\
 & = & \nminus(b,\prev(\next(d))) \\
 & = & \nminus(b,d) \\
\end{eqnarray*}$$
and thus $\nplus(d,c) = b$. But then
$$\begin{eqnarray*}
 &   & \next(b) \\
 & = & \next(\nplus(d,c)) \\
 & = & \nplus(\next(d),c) \\
 & = & \nplus(a,c)
\end{eqnarray*}$$
as claimed.

Next we show that (2) implies (1) by induction on $a$. For the base case $a = \zero$, if $b = \nplus(a,c) = c$ then $\nminus(b,\zero) = b = c$. For the inductive step, suppose the implication holds for some $a$, and suppose further that $b = \nplus(\next(a),c)$. Now
$$\begin{eqnarray*}
 &   & \nminus(b,\next(a)) \\
 & = & \nminus(\nplus(\next(a),c),\next(a)) \\
 & = & \nminus(\next(\nplus(a,c)),\next(a)) \\
 & = & \nminus(\nplus(a,c),a) \\
 & = & c
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now $\nminus$ inherits several properties from $\nplus$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then the following are equivalent.

1. $\nminus(\nplus(a,b),b) = a$.
2. If $\nminus(b,a) = \nminus(b,c) \in \nats$, then $a = c$.
3. If $\nminus(a,b) = \nminus(c,b) \in \nats$, then $a = c$.
4. If $\nminus(b,a) \in \nats$, then $\nminus(\next(b),a) = \next(\nminus(b,a))$.
5. If $\nminus(b,a) \in \nats$, then $\nminus(b,\nminus(b,a)) = a$.
6. If $\nminus(a,b) \in \nats$, then $\nminus(\nplus(a,c),b) = \nplus(\nminus(a,b),c)$.
</div>

<div class="proof"><p>
1. Note that $\nplus(a,b) = \nplus(a,b)$.
2. Say $$\nminus(b,a) = d = \nminus(b,c),$$ with $d \in \nats$. Now $$\nplus(a,d) = b = \nplus(c,d)$$ and thus $a = c$ as claimed.
3. Say $$\nminus(a,b) = d = \nminus(c,b),$$ with $d \in \nats$. Now $$a = \nplus(b,d) = c$$ as claimed.
4. Say $\nminus(b,a) = c$. Now $\nplus(a,c) = b$, so that $$\nplus(a,\next(c)) = \next(\nplus(a,c)) = \next(b).$$ Thus we have $$\nminus(\next(b),a) = \next(c) = \next(\nminus(b,a))$$ as claimed.
5. Say $\nminus(b,a) = c$. Now $b = \nplus(a,c)$, so that $a = \nminus(b,\nminus(b,a))$.
6. We proceed by induction on $c$. For the base case, note that $$\nminus(\nplus(a,c),b) = \nminus(a,b) = \nplus(\nminus(a,b),c)$$ as needed. For the inductive step, suppose the equality holds for some $c$. Then we have
$$\begin{eqnarray*}
 &   & \nminus(\nplus(a,\next(c)),b) \\
 & = & \nminus(\next(\nplus(a,c)),b) \\
 & = & \next(\nminus(\nplus(a,c),b)) \\
 & = & \next(\nplus(\nminus(a,b),c)) \\
 & = & \nplus(\nminus(a,b),\next(c))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally:

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\nminus(a,b) = \ast$, then $\nminus(b,a) \in \nats$.
</div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case $a = \zero$, if $\nminus(\zero,b) = \ast$ we have $b \neq \zero$ and $\nminus(b,\zero) = b \in \nats$.

For the inductive step, suppose the implication holds for all $b$ for some $a$. Suppose further that $\nminus(\next(a),b) = \ast$. If $b = \zero$, note that $\nminus(\next(a),\zero) = \zero$ is false, so the implication holds vacuously. If $b = \next(d)$, then we have $$\nminus(\next(a),b) = \nminus(\next(a),\next(d)) = \nminus(a,d).$$ By the induction hypothesis we have $$\nminus(d,a) = c,$$ so that $$\nminus(b,a) = \nminus(\next(d),\next(a)) = c.$$
</p></div>
</div>

One more.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. If $\nminus(a,b) \in \nats$, then $$\nminus(\ntimes(c,a),\ntimes(c,b)) = \ntimes(c,\nminus(a,b))$$ for all $c \in \nats$.
</div>

<div class="proof"><p>
We proceed by induction on $a$. For the base case $a = \zero$, suppose we have $\nminus(a,b) \in \nats$; then $b = \zero$. Now $$\nminus(\ntimes(c,a),(\ntimes(c,b)) = \nminus(\zero,\zero) = \zero$$ and $$\ntimes(c,\nminus(a,b)) = \ntimes(c,\zero) = \zero$$ as claimed.

For the inductive step, suppose the equality holds for some $a \in \nats$ and suppose that $\nminus(\next(a),b) \in \nats$. Then we have
$$\begin{eqnarray*}
 &   & \nminus(\ntimes(c,\next(a)),\ntimes(c,b)) \\
 & = & \nminus(\nplus(\ntimes(c,a),c),\ntimes(c,b)) \\
 & = & \nplus(\nminus(\ntimes(c,a),\ntimes(c,b)),c) \\
 & = & \nplus(\ntimes(c,\nminus(a,b)),c) \\
 & = & \ntimes(c,\next(\nminus(a,b))) \\
 & = & \ntimes(c,\nminus(\next(a),b))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Implementation and Testing
--------------------------

And some properties. Some of these are less nice because ``minus`` returns a ``Maybe t``.

> _test_minus_next :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_minus_next _ a b =
>   (minus (next a) (next b)) ==== (minus a b)
> 
> 
> _test_minus_zero_left :: (Natural n)
>   => n -> Nat n -> Bool
> _test_minus_zero_left _ a =
>   (minus zero (next a)) ==== Nothing
> 
> 
> _test_minus_zero_right :: (Natural n)
>   => n -> Nat n -> Bool
> _test_minus_zero_right _ a =
>   (minus a zero) ==== Just a
> 
> 
> _test_minus_plus :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_minus_plus _ a b =
>   (minus (plus a b) b) ==== Just a
> 
> 
> _test_minus_next_left :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_minus_next_left _ a b =
>   case minus b a of
>     Just c  -> (minus (next b) a) ==== Just (next c)
>     Nothing -> True
> 
> 
> _test_minus_swap :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_minus_swap _ a b =
>   case minus b a of
>     Just c  -> minus b c ==== Just a
>     Nothing -> True

And a suite:

> _test_minus ::
>   ( TypeName n, Natural n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_minus n maxSize numCases = do
>   testLabel ("minus: " ++ typeName n)
> 
>   let
>     args = stdArgs
>      { maxSuccess = numCases
>      , maxSize    = maxSize
>      }
> 
>   runTest args (_test_minus_next n)
>   runTest args (_test_minus_zero_left n)
>   runTest args (_test_minus_zero_right n)
>   runTest args (_test_minus_plus n)
>   runTest args (_test_minus_next_left n)
>   runTest args (_test_minus_swap n)

And the runner:

> main_minus :: IO ()
> main_minus = do
>   _test_minus (zero :: Unary) 100 100
