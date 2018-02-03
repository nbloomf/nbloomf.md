---
title: Addition
author: nbloomf
date: 2014-06-01
tags: arithmetic-made-difficult, literate-haskell
slug: plus
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Plus
>   ( plus, _test_plus, main_plus
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Functions
> import NaturalNumbers
> import SimpleRecursion

So far we've characterized the natural numbers via a unique mapping $$\natrec{\ast}{\ast} : \nats \rightarrow A,$$ and we defined another parameterized mapping $$\simprec{\ast}{\ast} : \nats \times A \rightarrow B.$$ From now on, when we want to define a mapping with one of these signatures, these prepackaged recursive maps may come in handy. What's more, we can use the universal properties of these maps to define them in terms of *desired behavior*.

Natural number addition has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define addition in terms of $\simprec{\ast}{\ast}$. To do this, we need to find mappings $\varphi : \nats \rightarrow \nats$ and $\mu : \nats \times \nats \times \nats \rightarrow \nats$ that make $\simprec{\varphi}{\mu}$ act like addition. For example, we want $\next$ to act like $+1$, and $$n = \zero + n = \simprec{\varphi}{\mu}(\zero,n) = \varphi(n),$$ and

$$\begin{eqnarray*}
(m+n)+1
 & = & (m+1)+n \\
 & = & \simprec{\varphi}{\mu}(\next(m),n) \\
 &     \href{@simprec@#def-simprec-next}
   = & \mu(m,n,\simprec{\varphi}{\mu}(m,n)) \\
 & = & \mu(m,n,m+n).
\end{eqnarray*}$$

With this in mind, we define a binary operation $\nplus$ on $\nats$ as follows.

:::::: definition ::
Let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \next(b)$. We then define $\nplus : \nats \times \nats \rightarrow \nats$ by $$\nplus = \simprec{\id}{\mu}.$$

In Haskell:

> plus :: (Natural n) => n -> n -> n
> plus = simpleRec id mu
>   where mu _ _ b = next b

::::::::::::::::::::

Since $\nplus$ is defined in terms of simple recursion, it is the unique solution to a set of functional equations.

:::::: corollary :::
[]{#cor-plus-up}[]{#cor-plus-up-zero}[]{#cor-plus-up-next}
$\nplus$ is the unique map $f : \nats \times \nats \rightarrow \nats$ with the property that for all $a,b \in \nats$, we have
$$\left\{\begin{array}{l}
 f(\zero,b) = b \\
 f(\next(a),b) = \next(f(a,b)).
\end{array}\right.$$

::: test :::::::::::

> _test_plus_zero_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_plus_zero_left _ f =
>   testName "f(0,b) == b" $
>   \b -> eq (f zero b) b
> 
> 
> _test_plus_next_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_plus_next_left _ f =
>   testName "f(next(a),b) == next(f(a,b))" $
>   \a b -> eq (f (next a) b) (next (f a b))

::::::::::::::::::::
::::::::::::::::::::

Next we establish a version of the universal property of $\nplus$ with the arguments reversed.

:::::: theorem :::::
[]{#thm-plus-zero-right}[]{#thm-plus-next-right}
The following hold for all natural numbers $a$ and $b$.

1. $\nplus(a,\zero) = a$.
2. $\nplus(a,\next(b)) = \next(\nplus(a,b))$.

::: proof ::::::::::
1. We proceed by induction on $a$. For the base case, we have $\nplus(\zero,\zero) = \zero$ by the universal property of $\nplus$. For the inductive step, suppose we have $\nplus(\a,\zero) = \a$ for some $\a \in \nats$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(\a),\zero) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \next(\nplus(\a,\zero)) \\
 &     \hyp{\nplus(\a,\zero) = \a}
   = & \next(\a)
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,\next(b)) = \next(b).$$ For the inductive step, suppose we have $\next(\nplus(\a,b)) = \nplus(\a,\next(b))$ for all $b$ for some $\a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\next(\a),\next(b)) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \next(\nplus(\a,\next(b))) \\
 &     \hyp{\next(\nplus(\a,b)) = \nplus(\a,\next(b))}
   = & \next(\next(\nplus(\a,b))) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \next(\nplus(\next(\a),b))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_plus_zero_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> Bool)
> _test_plus_zero_right _ f =
>   testName "plus(a,0) == a" $
>   \a -> eq (f a zero) a
> 
> 
> _test_plus_next_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_plus_next_right _ f =
>   testName "next(plus(a,b)) == plus(a,next(b))" $
>   \a b -> eq (f a (next b)) (next (f a b))

::::::::::::::::::::
::::::::::::::::::::

$\nplus$ is associative and commutative.

:::::: theorem :::::
[]{#thm-plus-associative}[]{#thm-plus-commutative}
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\nplus(\nplus(a,b),c) = \nplus(a,\nplus(b,c))$.
2. $\nplus(a,b) = \nplus(b,a)$.

::: proof ::::::::::
1. We will show this by induction on $a$. For the base case, note that $$\nplus(\nplus(\zero,b),c) = \nplus(b,c) = \nplus(\zero,\nplus(b,c)).$$ For the inductive step, suppose the result holds for some $\a$. Then
$$\begin{eqnarray*}
 &   & \nplus(\nplus(\next(\a),b),c) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \nplus(\next(\nplus(\a,b)),c) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \next(\nplus(\nplus(\a,b),c)) \\
 &     \hyp{\nplus(\a,\nplus(b,c)) = \nplus(\nplus(\a,b),c)}
   = & \next(\nplus(\a,\nplus(b,c))) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \nplus(\next(\a),\nplus(b,c))
\end{eqnarray*}$$
as needed.
2. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,b) = b = \nplus(b,\zero).$$ For the inductive step, suppose the result holds for some $\a$. Then we have
$$\begin{eqnarray*}
 &   & \nplus(\next(\a),b) \\
 &     \href{@plus@#cor-plus-up-next}
   = & \next(\nplus(\a,b)) \\
 &     \hyp{\nplus(\a,b) = \nplus(b,\a)}
   = & \next(\nplus(b,\a)) \\
 &     \href{@plus@#thm-plus-next-right}
   = & \nplus(b,\next(\a))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_plus_associative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_plus_associative _ f =
>   testName "plus(plus(a,b),c) == plus(a,plus(b,c))" $
>   \a b c -> eq (f (f a b) c) (f a (f b c))
> 
> 
> _test_plus_commutative :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> Bool)
> _test_plus_commutative _ f =
>   testName "plus(a,b) == plus(b,a)" $
>   \a b -> eq (f a b) (f b a)

::::::::::::::::::::
::::::::::::::::::::

And $\nplus$ is cancellative.

:::::: theorem :::::
The following hold for all natural numbers $a$, $b$, and $c$.

1. If $\nplus(c,a) = \nplus(c,b)$ then $a = b$.
2. If $\nplus(a,c) = \nplus(b,c)$ then $a = b$.

::: proof ::::::::::
1. We proceed by induction on $c$. For the base case, note that if $\nplus(\zero,a) = \nplus(\zero,b)$, then we have $$a = \nplus(\zero,a) = \nplus(\zero,b) = b.$$ For the inductive step, suppose the result holds for some $c$. Now if $$\nplus(\next(c),a) = \nplus(\next(c),b),$$ then $$\next(\nplus(c,a)) = \next(\nplus(c,b))$$ so that $$\nplus(c,a) = \nplus(c,b)$$ and thus $a = b$ as needed.
2. If $$\nplus(a,c) = \nplus(b,c),$$ then $$\nplus(c,a) = \nplus(c,b),$$ and so $a = b$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_plus_cancellative_left :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_plus_cancellative_left _ f =
>   testName "if plus(c,a) == plus(c,b) then a == b" $
>   \a b c -> if eq (f c a) (f c b)
>     then eq a b
>     else true
> 
> 
> _test_plus_cancellative_right :: (Natural n, Equal n)
>   => n -> (n -> n -> n) -> Test (n -> n -> n -> Bool)
> _test_plus_cancellative_right _ f =
>   testName "if plus(a,c) == plus(b,c) then a == b" $
>   \a b c -> if eq (f a c) (f b c)
>     then eq a b
>     else true

::::::::::::::::::::
::::::::::::::::::::

Of course we will eventually prefer to say $a + b$ instead of $\nplus(a,b)$. But we'll avoid the more familiar notation until we're convinced that $\nplus$ really does act just like the usual $+$, since familiar notation can easily lull us into using theorems we haven't proven yet.


Testing
-------

Suite:

> _test_plus
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n)
>   => n -> (n -> n -> n) -> Int -> Int -> IO ()
> _test_plus n f maxSize numCases = do
>   testLabel1 "plus" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_plus_zero_left n f)
>   runTest args (_test_plus_next_left n f)
>   runTest args (_test_plus_zero_right n f)
>   runTest args (_test_plus_next_right n f)
>   runTest args (_test_plus_associative n f)
>   runTest args (_test_plus_commutative n f)
>   runTest args (_test_plus_cancellative_left n f)
>   runTest args (_test_plus_cancellative_right n f)

Main:

> main_plus :: IO ()
> main_plus = do
>   _test_plus (zero :: Unary) plus 100 100
