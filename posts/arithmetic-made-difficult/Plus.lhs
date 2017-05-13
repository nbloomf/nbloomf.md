---
title: Addition
author: nbloomf
date: 2014-06-01
tags: arithmetic-made-difficult, literate-haskell
---

> module Plus
>   ( plus, _test_plus, main_plus
>   ) where
>
> import Booleans
> import NaturalNumbers
> 
> import Prelude(Show, IO, Bool(..), Int, sequence_, id)
> import Test.QuickCheck

So far we've characterized the natural numbers via a unique mapping $$\natrec{\ast}{\ast} : \nats \rightarrow A,$$ and we defined another parameterized mapping $$\simprec{\ast}{\ast} : \nats \times A \rightarrow B.$$ From now on, when we want to define a mapping with one of these signatures, these prepackaged recursive maps may come in handy. What's more, we can use the universal properties of these maps to define them in terms of *desired behavior*.

Natural number addition has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define addition in terms of $\simprec{\ast}{\ast}$. To do this, we need to find mappings $\varphi : \nats \rightarrow \nats$ and $\mu : \nats \times \nats \times \nats \rightarrow \nats$ that make $\simprec{\varphi}{\mu}$ act like addition. For example, we want $\next$ to act like $+1$, and $$n = \zero + n = \simprec{\varphi}{\mu}(\zero,n) = \varphi(n),$$ and

$$\begin{eqnarray*}
(m+n)+1
 & = & (m+1)+n \\
 & = & \simprec{\varphi}{\mu}(\next(m),n) \\
 & = & \mu(m,n,\simprec{\varphi}{\mu}(m,n)) \\
 & = & \mu(m,n,m+n).
\end{eqnarray*}$$

With this in mind, we define a binary operation $\nplus$ on $\nats$ as follows.

<div class="result">
<div class="defn"><p>
Let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \next(b)$. We then define $\nplus : \nats \times \nats \rightarrow \nats$ by $$\nplus = \simprec{\id}{\mu}.$$
</p></div>
</div>

Showing that $\nplus$ has the familiar properties of addition then comes down to a few applications of induction.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\nplus(\zero,a) = a = \nplus(a,\zero)$.
2. $\nplus(\next(a),b) = \next(\nplus(a,b)) = \nplus(a,\next(b))$.
3. $\nplus(\nplus(a,b),c) = \nplus(a,\nplus(b,c))$.
4. $\nplus(a,b) = \nplus(b,a)$.
5. If $\nplus(c,a) = \nplus(c,b)$ then $a = b$.
6. If $\nplus(a,c) = \nplus(b,c)$ then $a = b$.
</div>

<div class="proof"><p>
1. Note that $$\nplus(\zero,a) = \simprec{\id}{\mu}(\zero,a) = \id(a) = a.$$ We show the second equality by induction on $a$. For the base case, we have $\nplus(\zero,\zero) = \zero$ by the first equality. For the inductive step, suppose we have $\nplus(a,\zero) = a$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(a),\zero) \\
 & = & \simprec{\id}{\mu}(\next(a),\zero) \\
 & = & \mu(a, \zero, \simprec{\id}{\mu}(a,\zero)) \\
 & = & \mu(a, \zero, \nplus(a, \zero)) \\
 & = & \mu(a,\zero,a) \\
 & = & \next(a)
\end{eqnarray*}$$
as needed.
2. Note that
$$\begin{eqnarray*}
 &   & \nplus(\next(a),b) \\
 & = & \simprec{\id}{\mu}(\next(a),b) \\
 & = & \mu(a,b,\simprec{\id}{\mu}(a,b)) \\
 & = & \mu(a,b,\nplus(a,b)) \\
 & = & \next(\nplus(a,b)).
\end{eqnarray*}$$
We show the second equality by induction on $a$. For the base case, note that $$\begin{eqnarray*} & & \nplus(\zero,\next(b)) \\ & = & \simprec{\id}{\mu}(\zero,\next(b)) \\ & = & \id(\next(b)) \\ & = & \next(b). \end{eqnarray*}$$ For the inductive step, suppose we have $\next(\nplus(a,b)) = \nplus(a,\next(b))$ for some $a$. Then $$\begin{eqnarray*} & & \nplus(\next(a),\next(b)) \\ & = & \simprec{\id}{\mu}(\next(a),\next(b)) \\ & = & \mu(a, \next(b), \simprec{\id}{\mu}(a, \next(b))) \\ & = & \mu(a, \next(b), \nplus(a, \next(b))) \\ & = & \mu(a, \next(b), \next(\nplus(a,b))) \\ & = & \next(\next(\nplus(a,b))) \\ & = & \next(\nplus(\next(a),b)) \end{eqnarray*}$$ as needed.
3. We will show this by induction on $a$. For the base case, note that $$\nplus(\nplus(\zero,b),c) = \nplus(b,c) = \nplus(\zero,\nplus(b,c)).$$ For the inductive step, suppose the result holds for some $a$. Then $$\begin{eqnarray*} & & \nplus(\nplus(\next(a),b),c) \\ & = & \nplus(\next(\nplus(a,b)),c) \\ & = & \next(\nplus(\nplus(a,b),c)) \\ & = & \next(\nplus(a, \nplus(b,c))) \\ & = & \nplus(\next(a), \nplus(b,c)) \end{eqnarray*}$$ as needed.
4. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,b) = b = \nplus(b,\zero).$$ For the inductive step, suppose the result holds for some $a$. Then we have $$\begin{eqnarray*} & & \nplus(\next(a),b) \\ & = & \next(\nplus(a,b)) \\ & = & \next(\nplus(b,a)) \\ & = & \nplus(b, \next(a))\end{eqnarray*}$$ as needed.
5. We proceed by induction on $c$. For the base case, note that if $\nplus(\zero,a) = \nplus(\zero,b)$, then we have $$a = \nplus(\zero,a) = \nplus(\zero,b) = b.$$ For the inductive step, suppose the result holds for some $c$. Now if $$\nplus(\next(c),a)) = \nplus(\next(c),b),$$ then $$\next(\nplus(c,a)) = \next(\nplus(c,b))$$ so that $$\nplus(c,a) = \nplus(c,b)$$ and thus $a = b$ as needed.
6. Follows from (5) and (4).
</p></div>
</div>

Of course we will eventually prefer to say $a + b$ instead of $\nplus(a,b)$. But we'll avoid the more familiar notation until we're convinced that $\nplus$ really does act just like the familiar $+$, since familiar notation can easily lull us into using theorems we haven't proven yet.


Implementation and Testing
--------------------------

Here's ``plus``:

> plus :: (Natural t) => t -> t -> t
> plus = simpleRec id mu
>   where mu _ _ b = next b

We've proved a bunch of properties for ``plus``, but it's still a good idea to verify them. We can do this with ``QuickCheck``. First we express each property to be tested as a boolean function. Note that each one takes an "extra" argument; this is just to fix the type of the function being tested. (There may be a better way to do this.)

> -- a == plus(a,0) and a == plus(0,a)
> _test_plus_zero :: (Natural t)
>   => t -> Nat t -> Bool
> _test_plus_zero _ a =
>   (a ==== plus a zero) &&& (a ==== plus zero a)
> 
> 
> -- next(plus(a,b)) == plus(next(a),b)
> _test_plus_next_left :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_plus_next_left _ a b =
>   (next (plus a b)) ==== (plus (next a) b)
> 
> 
> -- next(plus(a,b)) == plus(a,next(b))
> _test_plus_next_right :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_plus_next_right _ a b =
>   (next (plus a b)) ==== (plus a (next b))
>   
> 
> -- plus(plus(a,b),c) == plus(a,plus(b,c))
> _test_plus_associative :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_plus_associative _ a b c =
>   (plus (plus a b) c) ==== (plus a (plus b c))
> 
> 
> -- plus(a,b) == plus(b,a)
> _test_plus_commutative :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_plus_commutative _ a b =
>   (plus a b) ==== (plus b a)

We'll wrap all these tests behind a single function, ``_test_plus``, which takes the number of cases to check as an argument.

> -- run all tests for plus
> _test_plus :: (Natural n, Arbitrary n, Show n)
>   => n -> Int -> Int -> IO ()
> _test_plus n maxSize numCases = sequence_
>   [ quickCheckWith args (_test_plus_zero n)
>   , quickCheckWith args (_test_plus_next_left n)
>   , quickCheckWith args (_test_plus_next_right n)
>   , quickCheckWith args (_test_plus_associative n)
>   , quickCheckWith args (_test_plus_commutative n)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

woo!

I will also provide a ``main`` function so my build scripts for this blog can automatically compile and run the tests.

> main_plus :: IO ()
> main_plus = _test_plus (zero :: Unary) 100 100
