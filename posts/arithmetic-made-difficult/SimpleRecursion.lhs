---
title: Simple Recursion
author: nbloomf
date: 2014-05-07
tags: arithmetic-made-difficult, literate-haskell
slug: simprec
---

> {-# LANGUAGE NoImplicitPrelude, BangPatterns #-}
> module SimpleRecursion
>   ( simpleRec, _test_simplerec, main_simplerec
>   ) where
> 
> import Testing
> import Tuples
> import Booleans
> import NaturalNumbers

So far we've defined the natural numbers as an iterative set with a special *universal property*, which was encapsulated in the existence of a simple recursion operator $\natrec$. Anything we will wish to do with the natural numbers can be done using this operator alone. However, in practice, it will be handy to define synonyms for some more complicated recursive functions; the first of these is *simple recursion with a parameter*.

:::::: theorem :::::
[]{#def-simprec-zero}[]{#def-simprec-next}
Suppose we have sets $A$ and $B$ and functions $\varphi : A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then there is a unique function $Θ : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$Θ(\zero,a) = \varphi(a)$$ and $$Θ(\next(n),a) = \mu(n,a,Θ(n,a)).$$

This function $Θ$ will be denoted $\simprec(\varphi)(\mu)$.

::: proof ::::::::::
First we establish existence. Define $\varepsilon : A \rightarrow \nats \times B$ by $$\varepsilon = \compose(\tup(\zero))(\varphi)$$ and define $\chi : A \rightarrow \nats \times B \rightarrow \nats \times B$ by $$\chi(a)(\tup(n)(b)) = \tup(\next(n))(\mu(n,a,b)).$$ Thinking of $(\nats \times B, \varepsilon(a), \chi(a))$ as an inductive set, we define $Ω : \nats \rightarrow A \rightarrow \nats \times B$ by $$Ω(n,a) = \natrec(\varepsilon(a))(\chi(a))(n)$$ and $Θ : \nats \times A \rightarrow B$ by $Θ(n,a) = \snd(Ω(n,a))$.

Now note that
$$\begin{eqnarray*}
 &   & Θ(\zero,a) \\
 &     \let{Θ(n,a) = \snd(\natrec(\varepsilon(a))(\chi(a))(n))}
   = & \snd(\natrec(\varepsilon(a))(\chi(a))(\zero)) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \snd(\varepsilon(a)) \\
 &     \hyp{\varepsilon(a) = \tup(\zero)(\varphi(a))}
   = & \snd(\tup(\zero)(\varphi(a))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \varphi(a)
\end{eqnarray*}$$
as claimed.

Next we show that $$Ω(\next(n),a) = \tup(\next(n))(\mu(n,a,Θ(n,a)))$$ for all $a \in A$ and $n \in \nats$ by induction on $n$. For the base case $n = \zero$, we have
$$\begin{eqnarray*}
 &   & Ω(\next(\zero),a) \\
 &     \let{Ω(n,a) = \natrec(\varepsilon(a))(\chi(a))(n)}
   = & \natrec(\varepsilon(a))(\chi(a))(\next(\zero)) \\
 &     \href{@peano@#cor-natrec-next}
   = & \chi(a)(\natrec(\varepsilon(a))(\chi(a))(\zero)) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \chi(a)(\varepsilon(a)) \\
 &     \hyp{\varepsilon(a) = \tup(\zero)(\varphi(a))}
   = & \chi(a)(\tup(\zero)(\varphi(a))) \\
 &     \hyp{\chi(a)(\tup(n)(b)) = \tup(\next(n))(\mu(n,a,b))}
   = & \tup(\next(\zero))(\mu(\zero,a,\varphi(a))) \\
 &     \hyp{Θ(\zero,a) = \varphi(a)}
   = & \tup(\next(\zero))(\mu(\zero,a,Θ(\zero,a)))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $n$. Now
$$\begin{eqnarray*}
 &   & Ω(\next(\next(n)),a) \\
 &     \let{Ω(n,a) = \natrec(\varepsilon(a))(\chi(a))(n)}
   = & \natrec(\varepsilon(a))(\chi(a))(\next(\next(n))) \\
 &     \href{@peano@#cor-natrec-next}
   = & \chi(a)(\natrec(\varepsilon(a))(\chi(a))(\next(n))) \\
 &     \let{Ω(n,a) = \natrec(\varepsilon(a))(\chi(a))(n)}
   = & \chi(a)(Ω(\next(n),a)) \\
 &     \hyp{Ω(\next(n),a) = \tup(\next(n))(\mu(n,a,Θ(n,a)))}
   = & \chi(a)(\tup(\next(n))(\mu(n,a,Θ(n,a)))) \\
 &     \hyp{\chi(a)(\tup(n)(b)) = \tup(\next(n))(\mu(n,a,b))}
   = & \tup(\next(\next(n)))(\mu(\next(n),a,\mu(n,a,Θ(n,a)))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \tup(\next(\next(n)))(\mu(\next(n),a,\snd(\tup(\next(n))(\mu(n,a,Θ(n,a)))))) \\
 &     \hyp{Ω(\next(n),a) = \tup(\next(n))(\mu(n,a,Θ(n,a)))}
   = & \tup(\next(\next(n)))(\mu(\next(n),a,\snd(Ω(\next(n),a)))) \\
 &     \hyp{Θ(n,a) = \snd(Ω(n,a))}
   = & \tup(\next(\next(n)))(\mu(\next(n),a,Θ(\next(n),a)))
\end{eqnarray*}$$
as needed. Thus for all $a$ and $n$ we have
$$\begin{eqnarray*}
 &   & Θ(\next(n),a) \\
 &     \hyp{Θ(n,a) = \snd(Ω(n,a))}
   = & \snd(Ω(\next(n),a)) \\
 &     \hyp{Ω(\next(n),a) = \tup(\next(n))(\mu(n,a,Θ(n,a)))}
   = & \snd(\tup(\next(n))(\mu(n,a,Θ(n,a)))) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \mu(n,a,Θ(n,a))
\end{eqnarray*}$$
as claimed.

To see that $Θ$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $Θ$. Then we have
$$\begin{eqnarray*}
 &   & \Psi(\zero,a) \\
 &     \hyp{\Psi(\zero,a) = \varphi(a)}
   = & \varphi(a) \\
 &     \hyp{Θ(\zero,a) = \varphi(a)}
   = & Θ(\zero,a)
\end{eqnarray*}$$
for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = Θ(n, a)$ for all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \Psi(\next(n),a) \\
 &     \hyp{\Psi(\next(n),a) = \mu(n,a,\Psi(n,a))}
   = & \mu(n,a,\Psi(n,a)) \\
 &     \hyp{\Psi(n,a) = Θ(n,a)}
   = & \mu(n,a,Θ(n,a)) \\
 &     \hyp{Θ(\next(n),a) = \mu(n,a,Θ(n,a))}
   = & Θ(\next(n),a)
\end{eqnarray*}$$
as needed. Thus $\Psi = Θ$.
::::::::::::::::::::
::::::::::::::::::::

That proof may look complicated, but structurally it's very simple. We defined $Θ$ and showed it has the claimed properties with induction, then we showed it is unique by induction.


Implementation
--------------

As we did with $\natrec(\ast)(\ast)$, we'd like to implement $\simprec(\ast)(\ast)$ in software. There are a couple of ways to go about this.

> simpleRec'', simpleRec', simpleRec :: (Natural n)
>   => (a -> b)
>   -> (n -> a -> b -> b)
>   -> n
>   -> a
>   -> b

There's the naive way:

> simpleRec'' phi mu n a = case unnext n of
>   Left () -> phi a
>   Right k -> mu k a $ simpleRec'' phi mu k a

There's the definition from the proof:

> simpleRec' phi mu n a = snd (naturalRec (epsilon a) (chi a) n)
>   where
>     epsilon b = tup zero (phi b)
>     chi c (Pair m b) = tup (next m) (mu m c b)

And the tail recursive strategy:

> simpleRec phi mu n a =
>   let
>     tau !x h m = case unnext m of
>       Left () -> x
>       Right k -> tau (mu h a x) (next h) k
>   in tau (phi a) zero n

While we're at it, we should test that these implementations are equivalent.

> _test_simplerec_equiv_def :: (Natural n, Equal b)
>   => n -> a -> b -> Test ((a -> b) -> (n -> a -> b -> b) -> n -> a -> Bool)
> _test_simplerec_equiv_def _ _ _ =
>   testName "simpleRec(phi,mu)(n,a) == simpleRec'(phi,mu)(n,a)" $
>   \phi mu n a -> eq (simpleRec phi mu n a) (simpleRec' phi mu n a)
> 
> _test_simplerec_equiv_naive :: (Natural n, Equal b)
>   => n -> a -> b -> Test ((a -> b) -> (n -> a -> b -> b) -> n -> a -> Bool)
> _test_simplerec_equiv_naive _ _ _ =
>   testName "simpleRec(phi,mu)(n,a) == simpleRec''(phi,mu)(n,a)" $
>   \phi mu n a -> eq (simpleRec phi mu n a) (simpleRec'' phi mu n a)

Some simple testing again shows that the tail recursive form is more efficient -- both of the other forms run out of space on medium-sized numbers. All we need to do is verify that the efficient ``simpRec`` is equivalent to the inefficient, but obviously correct, ``simpRec''``. We will (eventually) do this by induction.

First, though, we need a lemma about ``tau``. Note that in the definition of ``tau`` there are two implicit parameters, ``mu`` and ``a``. With ``mu`` and ``phi`` fixed, we define supplementary functions ``mu'`` and ``phi'`` as follows:

    mu' k a b = mu (N k) a b
    phi' a = mu Z a (phi a)

We will denote by ``tau'`` the version of ``tau`` where ``mu'`` is in scope, and by ``tau`` the version with ``mu`` in scope. We claim that

    tau' x h k == tau x (N h) k

for all ``x``, ``h``, and ``k``, and prove it by induction on ``k``. For the base case, note that

       tau' x h Z
    == x
    == tau x (N h) Z

For the inductive step, suppose the equation holds for ``k``. Then we have

       tau' x h (N k)
    == tau' (mu' h a x) (N h) k
    == tau (mu' h a x) (N $ N h) k
    == tau (mu (N h) a x) (N $ N h) k
    == tau x (N h) (N k)

as needed.

Next we claim that

    simpRec phi' mu' k a == simpRec phi mu (N k) a

for all ``phi``, ``mu``, ``k``, and ``a``. To see this, note that

       simpRec phi mu (N k) a
    == tau (phi a) Z (N k)
    == tau (mu Z a (phi a)) (N Z) k
    == tau' (mu Z a (phi a)) Z k
    == tau' (phi' a) Z k
    == simpRec phi' mu' k a

as needed. Also, ``simpRec''`` satisfies this equation, which we show by induction on ``k``. For the base case, note that

       simpRec'' phi' mu' Z a
    == phi' a
    == mu Z a (phi a)
    == mu Z a $ simpRec'' phi mu Z a
    == simpRec'' phi mu (N Z) a

And if the equation holds for ``k``, then we have

       simpRec'' phi' mu' (N k) a
    == mu' k a $ simpRec'' phi' mu' k a
    == mu' k a $ simpRec'' phi mu (N k) a
    == mu (N k) a $ simpRec'' phi mu (N k) a
    == simpRec'' phi mu (N $ N k) a

so that

    simpRec'' phi' mu' k a == simpRec'' phi mu (N k) a

for all ``phi``, ``mu``, ``k``, and ``a`` as claimed.

Finally we are prepared to show that ``simpRec == simpRec''``, by induction on ``k``. For the base case, we have

       simpRec'' phi mu Z a
    == phi a
    == tau (phi a) Z Z
    == simpRec phi mu Z a

And if the result holds for ``k``, we have

       simpRec'' phi mu (N k) a
    == simpRec'' phi' mu' k a
    == simpRec phi' mu' k a
    == simpRec phi mu (N k) a

So our efficient ``simpRec`` is equivalent to ``simpRec''``. (We will leave the equivalence of ``simpRec'`` and ``simpRec`` as an exercise.)


What it does
------------

This page is already long enough, so I'll save examples of simple recursion for another day. Just note what $\simprec(\ast)(\ast)$ does: given some data $\varphi$ and $\mu$, it produces a recursive function with signature $\nats \times A \rightarrow B$. So whenever we encounter (or want to construct) a function with this signature, it may be worthwhile to look for a definition in terms of $\simprec(\ast)(\ast)$. The uniqueness of simple recursion makes such functions very nice to reason about.

As with natural recursion, the "uniqueness" part of simple recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with $\varphi : \nats \times A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then $\simprec(\varphi)(\mu)$ is the unique solution $f : \nats \times A \rightarrow B$ to the following system of functional equations for all $k \in \nats$, $a \in A$, and $b \in B$:
$$\left\{\begin{array}{l}
 f(\zero,a) = \varphi(a) \\
 f(\next(k),a) = \mu(k,a,f(k,a))
\end{array}\right.$$
::::::::::::::::::::


Testing
-------

Suite:

> _test_simplerec
>   :: (TypeName n, Natural n, Equal n, Show n, Arbitrary n
>   , Equal b, Arbitrary a, CoArbitrary a, Arbitrary b, CoArbitrary b
>   , Show a, Show b, TypeName a, TypeName b, CoArbitrary n)
>   => n -> a -> b -> Int -> Int -> IO ()
> _test_simplerec n a b size cases = do
>   testLabel3 "simpleRec" n a b
> 
>   let
>     args = stdArgs
>       { maxSuccess = cases
>       , maxSize    = size
>       }
> 
>   runTest args (_test_simplerec_equiv_def n a b)
>   runTest args (_test_simplerec_equiv_naive n a b)

Main:

> main_simplerec :: IO ()
> main_simplerec = do
>   _test_simplerec (zero :: Unary) (true :: Bool)  (true :: Bool)  100 100
>   _test_simplerec (zero :: Unary) (zero :: Unary) (true :: Bool)  100 100
>   _test_simplerec (zero :: Unary) (true :: Bool)  (zero :: Unary) 100 100
>   _test_simplerec (zero :: Unary) (zero :: Unary) (zero :: Unary) 100 100
