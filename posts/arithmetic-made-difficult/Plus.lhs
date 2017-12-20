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
> import SimpleRecursion
> import Equals
> 
> import Prelude (id)
> import Test.QuickCheck
> import Test.QuickCheck.Test

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

In Haskell:

> plus :: (Natural t) => t -> t -> t
> plus = simpleRec id mu
>   where mu _ _ b = next b

</p></div>
</div>

Since $\nplus$ is defined in terms of simple recursion, it is the unique solution to a set of functional equations.

<div class="result">
<div class="thm"><p>
$\nplus$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have $$\left\{ \begin{array}{l} f(\zero,b) = b \\ f(\next(a),b) = \next(f(a,b)). \end{array} \right.$$
</p></div>

<div class="proof"><p>
That $\nplus$ is a solution falls out of the definition; note that
$$\begin{eqnarray*}
 &   & \nplus(\zero,b) \\
 & = & \simprec{\id}{\mu}(\zero,b) \\
 & = & \id(b) \\
 & = & b
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \nplus(\next(a),b) \\
 & = & \simprec{\id}{\mu}(\next(a),b) \\
 & = & \mu(a,b,\simprec{\id}{\mu}(a,b)) \\
 & = & \mu(a,b,\nplus(a,b)) \\
 & = & \next(\nplus(a,b)).
\end{eqnarray*}$$
as claimed.

To see uniqueness, note that under these conditions we have $$f = \simprec{\id}{\mu} = \nplus$$ as claimed.
</p></div>
</div>

Showing that $\nplus$ has the familiar properties of addition then comes down to a few applications of induction.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\nplus(a,\zero) = a$.
2. $\nplus(a,\next(b)) = \next(\nplus(a,b))$.
3. $\nplus(\nplus(a,b),c) = \nplus(a,\nplus(b,c))$.
4. $\nplus(a,b) = \nplus(b,a)$.
5. If $\nplus(c,a) = \nplus(c,b)$ then $a = b$.
6. If $\nplus(a,c) = \nplus(b,c)$ then $a = b$.
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. For the base case, we have $\nplus(\zero,\zero) = \zero$ by the first equality. For the inductive step, suppose we have $\nplus(a,\zero) = a$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(a),\zero) \\
 & = & \simprec{\id}{\mu}(\next(a),\zero) \\
 & = & \mu(a, \zero, \simprec{\id}{\mu}(a,\zero)) \\
 & = & \mu(a, \zero, \nplus(a, \zero)) \\
 & = & \mu(a,\zero,a) \\
 & = & \next(a)
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, note that
$$\begin{eqnarray*}
 &   & \nplus(\zero,\next(b)) \\
 & = & \simprec{\id}{\mu}(\zero,\next(b)) \\
 & = & \id(\next(b)) \\
 & = & \next(b).
\end{eqnarray*}$$
For the inductive step, suppose we have $\next(\nplus(a,b)) = \nplus(a,\next(b))$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(a),\next(b)) \\
 & = & \simprec{\id}{\mu}(\next(a),\next(b)) \\
 & = & \mu(a,\next(b),\simprec{\id}{\mu}(a, \next(b))) \\
 & = & \mu(a,\next(b),\nplus(a,\next(b))) \\
 & = & \mu(a,\next(b),\next(\nplus(a,b))) \\
 & = & \next(\next(\nplus(a,b))) \\
 & = & \next(\nplus(\next(a),b))
\end{eqnarray*}$$
as needed.
3. We will show this by induction on $a$. For the base case, note that $$\nplus(\nplus(\zero,b),c) = \nplus(b,c) = \nplus(\zero,\nplus(b,c)).$$ For the inductive step, suppose the result holds for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\nplus(\next(a),b),c) \\
 & = & \nplus(\next(\nplus(a,b)),c) \\
 & = & \next(\nplus(\nplus(a,b),c)) \\
 & = & \next(\nplus(a,\nplus(b,c))) \\
 & = & \nplus(\next(a),\nplus(b,c))
\end{eqnarray*}$$
as needed.
4. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,b) = b = \nplus(b,\zero).$$ For the inductive step, suppose the result holds for some $a$. Then we have
$$\begin{eqnarray*}
 &   & \nplus(\next(a),b) \\
 & = & \next(\nplus(a,b)) \\
 & = & \next(\nplus(b,a)) \\
 & = & \nplus(b,\next(a))
\end{eqnarray*}$$
as needed.
5. We proceed by induction on $c$. For the base case, note that if $\nplus(\zero,a) = \nplus(\zero,b)$, then we have $$a = \nplus(\zero,a) = \nplus(\zero,b) = b.$$ For the inductive step, suppose the result holds for some $c$. Now if $$\nplus(\next(c),a)) = \nplus(\next(c),b),$$ then $$\next(\nplus(c,a)) = \next(\nplus(c,b))$$ so that $$\nplus(c,a) = \nplus(c,b)$$ and thus $a = b$ as needed.
6. Follows from (5) and (4).
</p></div>
</div>

Of course we will eventually prefer to say $a + b$ instead of $\nplus(a,b)$. But we'll avoid the more familiar notation until we're convinced that $\nplus$ really does act just like the familiar $+$, since familiar notation can easily lull us into using theorems we haven't proven yet.


Testing
-------

We've proved a bunch of properties for ``plus``, but it's still a good idea to verify them. We can do this with ``QuickCheck``. First we express each property to be tested as a boolean function. Note that each one takes an "extra" argument; this is just to fix the type of the function being tested. (There may be a better way to do this.)

> _test_plus_zero :: (Natural t)
>   => t -> Test (Nat t -> Bool)
> _test_plus_zero _ =
>   testName "a == plus(a,0) and a == plus(0,a)" $
>   \a -> (a ==== plus a zero) &&& (a ==== plus zero a)
> 
> 
> _test_plus_next_left :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_plus_next_left _ =
>   testName "next(plus(a,b)) == plus(next(a),b)" $
>   \a b -> (next (plus a b)) ==== (plus (next a) b)
> 
> 
> _test_plus_next_right :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_plus_next_right _ =
>   testName "next(plus(a,b)) == plus(a,next(b))" $
>   \a b -> (next (plus a b)) ==== (plus a (next b))
> 
> 
> _test_plus_associative :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Nat n -> Bool)
> _test_plus_associative _ =
>   testName "plus(plus(a,b),c) == plus(a,plus(b,c))" $
>   \a b c -> (plus (plus a b) c) ==== (plus a (plus b c))
> 
> 
> _test_plus_commutative :: (Natural n)
>   => n -> Test (Nat n -> Nat n -> Bool)
> _test_plus_commutative _ =
>   testName "plus(a,b) == plus(b,a)" $
>   \a b -> (plus a b) ==== (plus b a)

We'll wrap all these tests behind a single function, ``_test_plus``, which takes the number of cases to check as an argument.

> -- run all tests for plus
> _test_plus :: (TypeName n, Natural n, Show n, Arbitrary n)
>   => n -> Int -> Int -> IO ()
> _test_plus n maxSize numCases = do
>   testLabel ("plus: " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_plus_zero n)
>   runTest args (_test_plus_next_left n)
>   runTest args (_test_plus_next_right n)
>   runTest args (_test_plus_associative n)
>   runTest args (_test_plus_commutative n)

woo!

I will also provide a ``main`` function so my build scripts for this blog can automatically compile and run the tests.

> main_plus :: IO ()
> main_plus = do
>   _test_plus (zero :: Unary) 100 100
