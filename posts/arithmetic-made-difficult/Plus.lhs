---
title: Addition
author: nbloomf
date: 2014-06-01
tags: arithmetic-made-difficult, literate-haskell
slug: plus
---

> module Plus
>   ( plus, _test_plus, main_plus
>   ) where
> 
> import Prelude ()
> import Booleans
> import NaturalNumbers
> import SimpleRecursion

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
<div class="corollary"><p>
$\nplus$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have $$\left\{ \begin{array}{l} f(\zero,b) = b \\ f(\next(a),b) = \next(f(a,b)). \end{array} \right.$$
</p></div>

<div class="test"><p>

> _test_plus_zero_left :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_plus_zero_left _ =
>   testName "plus(0,b) == b" $
>   \b -> eq (plus zero b) b
> 
> 
> _test_plus_next_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_plus_next_left _ =
>   testName "next(plus(a,b)) == plus(next(a),b)" $
>   \a b -> eq (next (plus a b)) (plus (next a) b)

</p></div>
</div>

Next we establish a version of the universal property of $\nplus$ with the arguments reversed.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$ and $b$.

1. $\nplus(a,\zero) = a$.
2. $\nplus(a,\next(b)) = \next(\nplus(a,b))$.
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. For the base case, we have $\nplus(\zero,\zero) = \zero$ by the universal property of $\nplus$. For the inductive step, suppose we have $\nplus(a,\zero) = a$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(a),\zero) \\
 & = & \next(\nplus(a,\zero)) \\
 & = & \next(a)
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,\next(b)) = \next(b).$$ For the inductive step, suppose we have $\next(\nplus(a,b)) = \nplus(a,\next(b))$ for all $b$ for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(a),\next(b)) \\
 & = & \next(\nplus(a,\next(b))) \\
 & = & \next(\next(\nplus(a,b))) \\
 & = & \next(\nplus(\next(a),b))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_plus_zero_right :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_plus_zero_right _ =
>   testName "plus(a,0) == a" $
>   \a -> eq (plus a zero) a
> 
> 
> _test_plus_next_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_plus_next_right _ =
>   testName "next(plus(a,b)) == plus(a,next(b))" $
>   \a b -> eq (plus a (next b)) (next (plus a b))

</p></div>
</div>

$\nplus$ is associative and commutative.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\nplus(\nplus(a,b),c) = \nplus(a,\nplus(b,c))$.
2. $\nplus(a,b) = \nplus(b,a)$.
</div>

<div class="proof"><p>
1. We will show this by induction on $a$. For the base case, note that $$\nplus(\nplus(\zero,b),c) = \nplus(b,c) = \nplus(\zero,\nplus(b,c)).$$ For the inductive step, suppose the result holds for some $a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\nplus(\next(a),b),c) \\
 & = & \nplus(\next(\nplus(a,b)),c) \\
 & = & \next(\nplus(\nplus(a,b),c)) \\
 & = & \next(\nplus(a,\nplus(b,c))) \\
 & = & \nplus(\next(a),\nplus(b,c))
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,b) = b = \nplus(b,\zero).$$ For the inductive step, suppose the result holds for some $a$. Then we have
$$\begin{eqnarray*}
 &   & \nplus(\next(a),b) \\
 & = & \next(\nplus(a,b)) \\
 & = & \next(\nplus(b,a)) \\
 & = & \nplus(b,\next(a))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_plus_associative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_plus_associative _ =
>   testName "plus(plus(a,b),c) == plus(a,plus(b,c))" $
>   \a b c -> eq (plus (plus a b) c) (plus a (plus b c))
> 
> 
> _test_plus_commutative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_plus_commutative _ =
>   testName "plus(a,b) == plus(b,a)" $
>   \a b -> eq (plus a b) (plus b a)

</p></div>
</div>

And $\nplus$ is cancellative.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. If $\nplus(c,a) = \nplus(c,b)$ then $a = b$.
2. If $\nplus(a,c) = \nplus(b,c)$ then $a = b$.
</div>

<div class="proof"><p>
1. We proceed by induction on $c$. For the base case, note that if $\nplus(\zero,a) = \nplus(\zero,b)$, then we have $$a = \nplus(\zero,a) = \nplus(\zero,b) = b.$$ For the inductive step, suppose the result holds for some $c$. Now if $$\nplus(\next(c),a)) = \nplus(\next(c),b),$$ then $$\next(\nplus(c,a)) = \next(\nplus(c,b))$$ so that $$\nplus(c,a) = \nplus(c,b)$$ and thus $a = b$ as needed.
2. If $$\nplus(a,c) = \nplus(b,c),$$ then $$\nplus(c,a) = \nplus(c,b),$$ and so $a = b$ as claimed.
</p></div>

<div class="test"><p>

> _test_plus_cancellative_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_plus_cancellative_left _ =
>   testName "if plus(c,a) == plus(c,b) then a == b" $
>   \a b c -> if eq (plus c a) (plus c b)
>     then eq a b
>     else True
> 
> 
> _test_plus_cancellative_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_plus_cancellative_right _ =
>   testName "if plus(a,c) == plus(b,c) then a == b" $
>   \a b c -> if eq (plus a c) (plus b c)
>     then eq a b
>     else True

</p></div>
</div>

Of course we will eventually prefer to say $a + b$ instead of $\nplus(a,b)$. But we'll avoid the more familiar notation until we're convinced that $\nplus$ really does act just like the usual $+$, since familiar notation can easily lull us into using theorems we haven't proven yet.


Testing
-------

> _test_plus
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n)
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
>   runTest args (_test_plus_zero_left n)
>   runTest args (_test_plus_next_left n)
>   runTest args (_test_plus_zero_right n)
>   runTest args (_test_plus_next_right n)
>   runTest args (_test_plus_associative n)
>   runTest args (_test_plus_commutative n)
>   runTest args (_test_plus_cancellative_left n)
>   runTest args (_test_plus_cancellative_right n)

woo!

> main_plus :: IO ()
> main_plus = do
>   _test_plus (zero :: Unary) 100 100
