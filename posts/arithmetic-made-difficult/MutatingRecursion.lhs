---
title: Mutating Recursion
author: nbloomf
date: 2014-05-22
tags: arithmetic-made-difficult, literate-haskell
slug: mutrec
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module MutatingRecursion
>   ( mutatingRec, _test_mutatingrec, main_mutatingrec
>   ) where
> 
> import Testing
> import Booleans
> import DisjointUnions
> import NaturalNumbers

Note that both simple recursion and bailout recursion produce functions with type $$\nats \times A \rightarrow B;$$ we can call that $A$ argument the *parameter*. Now simple and bailout recursion use the parameter in different ways. Simple recursion is only allowed to change $A$ "outside" the recursive call, while bailout recursion can only change $A$ "inside" the recursive call. These restrictions were necessary so that simple and bailout recursion would have tail-recursive implementations. But there are times when we will want a recursive function with signature $\nats \times A \rightarrow B$ that can change its $A$ parameter both inside and outside the recursion.

For this situation we introduce yet another recursion operator on $\nats$, which we'll call *mutating recursion*.

:::::: theorem :::::
[]{#thm-mutrec-zero}[]{#thm-mutrec-next}
Let $A$ and $B$ be sets. Suppose we have mappings $\varepsilon : A \rightarrow B$, $\beta : \nats \times A \rightarrow B$, $\psi : \nats \times A \rightarrow B$, $\chi : \nats \times A \times B \rightarrow B$, and $\omega : \nats \times A \rightarrow A$. Then there is a unique map $Θ : \nats \times A \rightarrow B$ such that $$Θ(\zero,a) = \varepsilon(a)$$ and $$Θ(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,Θ(n,\omega(n,a)))}.$$ We denote this $Θ$ by $\mutrec{\varepsilon}{\beta}{\psi}{\chi}{\omega}$.

::: proof ::::::::::
Define $δ \in B^{A \times \nats}$ by $$δ(a,n) = \varepsilon(a)$$ and $σ : B^{A \times \nats} \rightarrow B^{A \times \nats}$ by $$σ(g)(a,n) = \bif{\beta(\prev(n),a)}{\psi(\prev(n),a)}{\chi(\prev(n),a,g(\omega(\prev(n),a)),\prev(n))}.$$ Now $(B^{A \times \nats},δ,σ)$ is an iterative set. We now define $$Θ(n,a) = \natrec(δ)(σ)(n)(\tup(a)(n)).$$

To see that $Θ$ has the claimed properties, note that
$$\begin{eqnarray*}
 &   & Θ(\zero,a) \\
 &     \let{Θ(n,a) = \natrec(δ)(σ)(n)(\tup(a)(n))}
   = & \natrec(δ)(σ)(\zero)(\tup(a)(\zero)) \\
 &     \href{@peano@#cor-natrec-zero}
   = & δ(\tup(a)(\zero)) \\
 &     \let{δ(\tup(a)(n)) = \varepsilon(a)}
   = & \varepsilon(a)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & Θ(\next(n),a) \\
 &     \let{Θ(n,a) = \natrec(δ)(σ)(n)(\tup(a)(n))}
   = & \natrec(δ)(σ)(\next(n))(\tup(a)(\next(n))) \\
 &     \href{@peano@#cor-natrec-next}
   = & σ(\natrec(δ)(σ)(n))(\tup(a)(\next(n))) \\
 &     \let{σ(g)(\tup(a)(n)) = \bif{\beta(\prev(n),a)}{\psi(\prev(n),a)}{\chi(\prev(n),a,g(\omega(\prev(n),a),\prev(n)))}}
   = & \bif{\beta(\prev(\next(n)),a)}{\psi(\prev(\next(n)),a)}{\chi(\prev(\next(n)),a,\natrec(δ)(σ)(n)(\omega(\prev(\next(n)),a),\prev(\next(n))))} \\
 &     \href{@unary@#thm-prev-next}
   = & \bif{\beta(n,a)}{\psi(\prev(\next(n)),a)}{\chi(\prev(\next(n)),a,\natrec(δ)(σ)(n)(\omega(\prev(\next(n)),a),\prev(\next(n))))} \\
 &     \href{@unary@#thm-prev-next}
   = & \bif{\beta(n,a)}{\psi(\prev(\next(n)),a)}{\chi(n,a,\natrec(δ)(σ)(n)(\omega(\prev(\next(n)),a),\prev(\next(n))))} \\
 &     \href{@unary@#thm-prev-next}
   = & \bif{\beta(n,a)}{\psi(\prev(\next(n)),a)}{\chi(n,a,\natrec(δ)(σ)(n)(\omega(n,a),\prev(\next(n))))} \\
 &     \href{@unary@#thm-prev-next}
   = & \bif{\beta(n,a)}{\psi(\prev(\next(n)),a)}{\chi(n,a,\natrec(δ)(σ)(n)(\omega(n,a),n))} \\
 &     \href{@unary@#thm-prev-next}
   = & \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,\natrec(δ)(σ)(n)(\omega(n,a),n))}
\end{eqnarray*}$$
as claimed.

Now we show that $Θ$ is unique with this property. To that end, suppose $\Psi$ does as well; we show that $Θ(n,a) = \Psi(n,a)$ for all $n$ by induction. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & Θ(\zero,a) \\
 &     \hyp{Θ(\zero,a) = \varepsilon(a)}
   = & \varepsilon(a) \\
 &     \hyp{\Psi(\zero,a) = \varepsilon(a)}
   = & \Psi(\zero,a)
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for all $a$ for some $n$. Now
$$\begin{eqnarray*}
 &   & Θ(\next(n),a) \\
 &     \hyp{Θ(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,Θ(n,\omega(n,a)))}}
   = & \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,Θ(n,\omega(n,a)))} \\
 &     \hyp{Θ(n,a) = \Psi(n,a)}
   = & \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,\Psi(n,\omega(n,a)))} \\
 &     \hyp{\Psi(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,\Psi(n,\omega(n,a)))}}
   = & \Psi(\next(n),a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

As usual we now want to implement $\mutrec{\ast}{\ast}{\ast}{\ast}{\ast}$ in software, and there are a couple of ways to go about this. First, the signature.

> mutatingRec, mutatingRec' :: (Natural n, Boolean bool)
>   => (a -> b)
>   -> (n -> a -> bool)
>   -> (n -> a -> b)
>   -> (n -> a -> b -> b)
>   -> (n -> a -> a)
>   -> n
>   -> a
>   -> b

There's the naive way:

> mutatingRec epsilon beta psi chi omega n a =
>   case unnext n of
>     Left () -> epsilon a
>     Right m -> ifThenElse (beta m a)
>       (psi m a)
>       (chi m a (mutatingRec epsilon beta psi chi omega m (omega m a)))

And there's the definition from the proof:

> mutatingRec' epsilon beta psi chi omega n a =
>   naturalRec delta sigma n (a,n)
>   where
>     delta (b,_) = epsilon b
> 
>     sigma g (b,m) = ifThenElse (beta (prev m) b)
>       (psi (prev m) b)
>       (chi (prev m) b (g (omega (prev m) b, (prev m))))

The naive implementation of mutating recursion is not tail recursive, and I think (without proof) that no truly tail recursive implementation exists (that is sort of the reason for this operator).

While we're at it, we should test that the two are not *not* equivalent.

> _test_mutatingrec_equiv :: (Natural n, Boolean bool, Equal b)
>   => n -> a -> b -> bool
>   -> Test ((a -> b) -> (n -> a -> bool) -> (n -> a -> b) -> (n -> a -> b -> b) -> (n -> a -> a) -> n -> a -> Bool)
> _test_mutatingrec_equiv _ _ _ _ =
>   testName "mutatingRec(delta,beta,psi,chi,omega)(n,a) == mutatingRec'(delta,beta,psi,chi,omega)(n,a)" $
>   \delta beta psi chi omega n a -> eq
>     (mutatingRec delta beta psi chi omega n a)
>     (mutatingRec' delta beta psi chi omega n a)


What it does
------------

As with the other recursion operators, the "uniqueness" part of mutating recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with mappings
$$\begin{eqnarray*}
 \varepsilon & : & A \rightarrow B \\
 \beta & : & \nats \times A \rightarrow \bool \\
 \psi & : & \nats \times A \rightarrow B \\
 \chi & : & \nats \times A \times B \rightarrow B \\
 \omega & : & \nats \times A \rightarrow A.
\end{eqnarray*}$$
Then $\mutrec{\varepsilon}{\beta}{\psi}{\chi}{\omega}$ is the unique solution $f : \nats \times A \rightarrow B$ to the following system of functional equations for all $k \in \nats$, $a \in A$:
$$\left\{\begin{array}{l}
 f(\zero,a) = \varepsilon(a) \\
 f(\next(n),a) = \bif{\beta(n,a)}{\psi(n,a)}{\chi(n,a,f(n,\omega(n,a)))}
\end{array}\right.$$
::::::::::::::::::::


Testing
-------

Suite:

> _test_mutatingrec
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , Equal b, Arbitrary a, CoArbitrary a, Arbitrary b, CoArbitrary b
>   , Boolean bool, Arbitrary bool
>   , Show a, Show b, TypeName a, TypeName b, CoArbitrary n)
>   => n -> a -> b -> bool -> Int -> Int -> IO ()
> _test_mutatingrec n a b p size cases = do
>   testLabel3 "mutatingRec" n a b
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_mutatingrec_equiv n a b p)

Main:

> main_mutatingrec :: IO ()
> main_mutatingrec = do
>   _test_mutatingrec (zero :: Unary) (true :: Bool)  (true :: Bool)  (true :: Bool) 50 500
>   _test_mutatingrec (zero :: Unary) (zero :: Unary) (true :: Bool)  (true :: Bool) 50 500
>   _test_mutatingrec (zero :: Unary) (true :: Bool)  (zero :: Unary) (true :: Bool) 50 500
>   _test_mutatingrec (zero :: Unary) (zero :: Unary) (zero :: Unary) (true :: Bool) 50 500
