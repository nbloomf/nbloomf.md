---
title: Bailout Recursion
author: nbloomf
date: 2014-05-21
tags: arithmetic-made-difficult, literate-haskell
slug: bailrec
---

> {-# LANGUAGE NoImplicitPrelude, BangPatterns #-}
> module BailoutRecursion
>   ( bailoutRec, _test_bailoutrec, main_bailoutrec
>   ) where
> 
> import Testing
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers

So far we have defined two special *recursion operators*, $\natrec(\ast)(\ast)$ and $\simprec$. These act like program skeletons: fill in the slots with functions of the right signatures and get a computable function out. In this post we'll define another operator, which we will call *bailout recursion*.

:::::: theorem :::::
[]{#thm-bailrec-zero}[]{#thm-bailrec-next}
Suppose we have sets $A$ and $B$ and functions with the following signatures:
$$\begin{eqnarray*}
\varphi & : & A \rightarrow B \\
\beta & : & \nats \times A \rightarrow \bool \\
\psi & : & \nats \times A \rightarrow B \\
\omega & : & \nats \times A \rightarrow A.
\end{eqnarray*}$$

Then there is a unique function $\Theta : \nats \rightarrow A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$\Theta(\zero,a) = \varphi(a)$$ and $$\Theta(\next(m),a) = \left\{ \begin{array}{ll} \psi(m,a) & \mathrm{if}\ \beta(m,a) \\ \Theta(m, \omega(m,a)) & \mathrm{otherwise}. \end{array}\right.$$

This function $\Theta$ will be denoted $\bailrec{\varphi}{\beta}{\psi}{\omega}$.

::: proof ::::::::::
We define $ε : \nats \times A \rightarrow A + (\nats \times A)$ by $ε(\tup(n)(a)) = \lft(a)$ and $\chi : (A + (\nats \times A))^{\nats \times A} \rightarrow (A + (\nats \times A))^{\nats \times A}$ by $$\chi(h)(\tup(n)(a)) = \bif{\beta(\prev(n),a)}{\rgt(\tup(\prev(n))(a))}{h(\prev(n),\omega(\prev(n),a))}.$$ Now thinking of $((A+(\nats \times A))^{\nats \times A},ε,\chi)$ as an inductive set, we define $Θ : \nats \times A \rightarrow B$ by $$Θ(n,a) = \either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a))).$$

To see that $Θ$ has the claimed properties, note that
$$\begin{eqnarray*}
 &   & Θ(\zero,a) \\
 &     \let{Θ(n,a) = \either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a)))}
   = & \either(\varphi,\psi)(\natrec(ε)(\chi)(\zero)(\tup(\zero)(a))) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \either(\varphi,\psi)(ε(\tup(\zero)(a))) \\
 &     \hyp{ε(\tup(n)(a)) = \lft(a)}
   = & \either(\varphi,\psi)(\lft(a)) \\
 &     \href{@disjoint-unions@#def-either-lft}
   = & \varphi(a)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & Θ(\next(n),a) \\
 &     \let{Θ(n,a) = \either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a)))}
   = & \either(\varphi,\psi)(\natrec(ε)(\chi)(\next(n))(\tup(\next(n))(a))) \\
 &     \href{@peano@#cor-natrec-next}
   = & \either(\varphi,\psi)(\chi(\natrec(ε)(\chi)(n))(\tup(\next(n))(a))) \\
 &     \hyp{\chi(h)(\tup(n)(a)) = \bif{\beta(\prev(n),a)}{\rgt(\tup(\prev(n))(a))}{h(\tup(\prev(n))(a))}}
   = & \either(\varphi,\psi)(\bif{\beta(\prev(\next(n)),a)}{\rgt(\tup(\prev(\next(n)))(a))}{\natrec(ε)(\chi)(n)(\tup(\prev(\next(n)))(a))}) \\
 &     \href{@unary@#thm-prev-next}
   = & \either(\varphi,\psi)(\bif{\beta(n,a)}{\rgt(\tup(\prev(\next(n)))(a))}{\natrec(ε)(\chi)(n)(\tup(\prev(\next(n)))(a))}) \\
 &     \href{@unary@#thm-prev-next}
   = & \either(\varphi,\psi)(\bif{\beta(n,a)}{\rgt(\tup(n)(a))}{\natrec(ε)(\chi)(n)(\tup(\prev(\next(n)))(a))}) \\
 &     \href{@unary@#thm-prev-next}
   = & \either(\varphi,\psi)(\bif{\beta(n,a)}{\rgt(\tup(n)(a))}{\natrec(ε)(\chi)(n)(\tup(n)(a))}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{\beta(n,a)}{\either(\varphi,\psi)(\rgt(\tup(n)(a)))}{\either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a)))} \\
 &     \href{@disjoint-unions@#def-either-rgt}
   = & \bif{\beta(n,a)}{\psi(\tup(n)(a))}{\either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a)))} \\
 &     \let{Θ(n,a) = \either(\varphi,\psi)(\natrec(ε)(\chi)(n)(\tup(n)(a)))}
   = & \bif{\beta(n,a)}{\psi(\tup(n)(a))}{Θ(n,a)}
\end{eqnarray*}$$

Next suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $\Theta$; we show that $\Psi = \Theta$ by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & \Psi(\zero,a) \\
 &     \hyp{\Psi(\zero,a) = \varphi(a)}
   = & \varphi(a) \\
 &     \hyp{\Theta(\zero,a) = \varphi(a)}
   = & \Theta(\zero,a)
\end{eqnarray*}$$
for all $a \in A$. For the inductive step, suppose the equality holds for some $n$, and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \Psi(\next(n),a) \\
 &     \hyp{\Psi(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\Psi(n,\omega(n,a))}}
   = & \bif{\beta(n,a)}{\psi(n,a)}{\Psi(n,\omega(n,a))} \\
 &     \hyp{\Psi(n,a) = \Theta(n,a)}
   = & \bif{\beta(n,a)}{\psi(n,a)}{\Theta(n,\omega(n,a))} \\
 &     \hyp{\Theta(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\Theta(n,\omega(n,a))}}
   = & \Theta(\next(n),a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::

You might notice that in this proof, we didn't really use $\beta$ or $\psi$. When this happens in a proof it usually means we've got some unnecessary details. But in this case, we will be using $\beta$ and $\psi$ later, and the piecewiseness of $\Theta$ will be crucial in constructing an efficient tail-recursive evaluation strategy.


Implementation
--------------

As we did with $\natrec(\ast)(\ast)$ and $\simprec$, we'd like to implement $\bailrec{\ast}{\ast}{\ast}{\ast}$ in software. There are a couple of ways to go about this. First, the signature.

> bailoutRec, bailoutRec' :: (Natural n)
>   => (a -> b)
>   -> (n -> a -> Bool)
>   -> (n -> a -> b)
>   -> (n -> a -> a)
>   -> n
>   -> a
>   -> b

There's the naive way:

> bailoutRec phi beta psi omega =
>   let
>     theta n a = case unnext n of
>       Left () -> phi a
>       Right m ->
>         if beta m a
>           then psi m a
>           else theta m (omega m a)
> 
>   in theta

And there's the definition from the proof:

> bailoutRec' phi beta psi omega n a =
>   either phi (uncurry psi) (naturalRec epsilon chi n (tup n a))
>   where
>     epsilon (Pair _ b) = lft b
>     chi h (Pair m b) = if beta (prev m) b
>       then rgt (tup (prev m) b)
>       else h (tup (prev m) (omega (prev m) b))

Unlike simple recursion, the naive implementation of bailout recursion is already tail recursive.

We should test that these are equivalent:

> _test_bailoutrec_equiv :: (Natural n, Equal b)
>   => n -> a -> b -> Test ((a -> b) -> (n -> a -> Bool) -> (n -> a -> b) -> (n -> a -> a) -> n -> a -> Bool)
> _test_bailoutrec_equiv _ _ _ =
>   testName "bailoutRec(phi,beta,psi,omega)(n,a) == bailoutRec'(phi,beta,psi,omega)(n,a)" $
>   \phi beta psi omega n a -> eq
>     (bailoutRec phi beta psi omega n a)
>     (bailoutRec' phi beta psi omega n a)


What it does
------------

Bailout recursion does some cool things that simple recursion does not. The $\omega$ map lets us "mutate" the initial parameter $a$ at each step in the recursion, and the boolean-valued function $\beta$ lets us short-circuit the recursion.

Also note that simple recursion and bailout recursion were carefully chosen to have *tail recursive* evaluation strategies. Roughly speaking, a recursive function is called *tail recursive* if there is "nothing left to do" after the recursive call. For example, $$f(n+1) = 1 + f(n)$$ is *not* tail recursive, because on the right hand side there is something waiting for the result of the recursive evaluation -- in this case, the $1+$.

Arbitrary recursion is dangerous because in general, every time one function uses another we have to keep track of what remains to be done afterward -- if we aren't careful, it is very easy to write recursive functions which eat up lots of memory. Even simple recursion can blow up exponentially; the classic example is the Fibonacci numbers (which we'll see later).

In contrast, a *tail recursive* function by definition doesn't have to keep track of what remains to be done after the recursion. Our recursion operators, $\natrec(\ast)(\ast)$, $\simprec$, and $\bailrec{\ast}{\ast}{\ast}{\ast}$, are carefully chosen so that they have tail recursive implementations.

By the way, I think it's helpful to compare the difference between arbitrary recursion and recursion operators to the difference between arbitrary ``GOTO``s and structured loops. In both cases we have a simple but dangerous primitive operation that is hidden behind a safer and more meaningful interface. A ``for`` loop means "repeat this some number of times"; while the meaning of simple recursion is given by its universal property.

As with natural and simple recursion, the "uniqueness" part of bailout recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with mappings
$$\begin{eqnarray*}
\varphi & : & A \rightarrow B \\
\beta & : & \nats \times A \rightarrow \bool \\
\psi & : & \nats \times A \rightarrow B \\
\omega & : & \nats \times A \rightarrow A.
\end{eqnarray*}$$
Then $\bailrec{\varphi}{\beta}{\psi}{\omega}$ is the unique solution $f : \nats \times A \rightarrow B$ to the following system of functional equations for all $k \in \nats$, $a \in A$:
$$\left\{\begin{array}{l}
 f(\zero,a) = \varphi(a) \\
 f(\next(k),a) = \bif{\beta(k,a)}{\psi(m,a)}{f(k,\omega(k,a))}
\end{array}\right.$$
::::::::::::::::::::


Testing
-------

Suite:

> _test_bailoutrec
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , Equal b, Arbitrary a, CoArbitrary a, Arbitrary b, CoArbitrary b
>   , Show a, Show b, TypeName a, TypeName b, CoArbitrary n)
>   => n -> a -> b -> Int -> Int -> IO ()
> _test_bailoutrec n a b size cases = do
>   testLabel3 "bailoutRec" n a b
> 
>   let
~ args = testArgs size cases
> 
>   runTest args (_test_bailoutrec_equiv n a b)

Main:

> main_bailoutrec :: IO ()
> main_bailoutrec = do
>   _test_bailoutrec (zero :: Unary) (true :: Bool)  (true :: Bool)  100 100
>   _test_bailoutrec (zero :: Unary) (zero :: Unary) (true :: Bool)  100 100
>   _test_bailoutrec (zero :: Unary) (true :: Bool)  (zero :: Unary) 100 100
>   _test_bailoutrec (zero :: Unary) (zero :: Unary) (zero :: Unary) 100 100
