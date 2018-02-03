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
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import Tuples
> import NaturalNumbers

So far we've defined the natural numbers as an iterative set with a special *universal property*, which was encapsulated in the existence of a simple recursion operator $\natrec{\ast}{\ast}$. Anything we will wish to do with the natural numbers can be done using this operator alone. However, in practice, it will be handy to define synonyms for some more complicated recursive functions; the first of these is *simple recursion with a parameter*.

:::::: theorem :::::
[]{#def-simprec-zero}[]{#def-simprec-next}
Suppose we have sets $A$ and $B$ and functions $\varphi : A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then there is a unique function $Θ : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$Θ(\zero,a) = \varphi(a)$$ and $$Θ(\next(n),a) = \mu(n,a,Θ(n,a)).$$

This function $Θ$ will be denoted $\simprec{\varphi}{\mu}$.

::: proof ::::::::::
First we establish existence. Define a map $$q : \nats \rightarrow {}^AB \rightarrow A \rightarrow B$$ by $$q(n)(h)(x) = \mu(n,x,h(x)),$$ and define $t : \nats \times {}^AB \rightarrow \nats \times {}^AB$ by $$t(n,h) = \tup(\next(n))(q(n)(h)).$$ Now we define $Θ$ as follows: $$Θ(n,a) = \compose(\snd)(\natrec{\tup(\zero)(\varphi)}{t})(n)(a).$$

Note that
$$\begin{eqnarray*}
 &   & Θ(\zero,a) \\
 &     \let{Θ(n,a) = \compose(\snd)(\natrec{\tup(\zero)(\varphi)}{t})(n)(a)}
   = & \compose(\snd)(\natrec{\tup(\zero)(\varphi)}{t})(\zero)(a) \\
 &     \href{@functions@#def-compose}
   = & \snd(\natrec{\tup(\zero)(\varphi)}{t}(\zero))(a) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \snd(\tup(\zero)(\varphi))(a) \\
 &     \href{@tuples@#thm-snd-tup}
   = & \varphi(a)
\end{eqnarray*}$$
as claimed.

Next we define an auxiliary map $w : \nats \rightarrow A \rightarrow B$ by $w(n)(x) = Θ(n,x)$. Note that
$$\begin{eqnarray*}
 &   & w(\zero)(x) \\
 & = & Θ(\zero,x) \\
 & = \varphi(x)
\\end{eqnarray*}$$
As an intermediate result, we also claim that $$q(n)(w(n)) = w(\next(n));$$ we show this by induction on $n$. For the base case $n = \zero$, if $x \in A$ we have
$$\begin{eqnarray*}
 &   & q(\zero)(w(\zero))(x) \\
 & = & \mu(\zero,x,w(\zero)(x)) \\
 & = & 
\end{eqnarray*}$$


To see the second property of $Θ$, we will show by induction that the following (compound) statement holds for all $n \in \nats$:

1. $\natrec{\tup(\zero)(\varphi)}{t}(n) = \tup(n)(w(n))$ and
2. $Θ(\next(n),a) = \mu(n,a,Θ(n,a))$ for all $a \in A$.

For the base case, note that

$$\begin{eqnarray*}
 &   & \natrec{\tup(\zero)(\varphi)}{t}(\zero) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \tup(\zero)(\varphi) \\
 &     \hyp{w(\zero) = \varphi}
   = & \tup(\zero)(w(\zero)) \\
\end{eqnarray*}$$

and that for all $a \in A$,

$$\begin{eqnarray*}
 &   & Θ(\next(\zero),a) \\
 &     \let{Θ(n,a) = \compose(\snd)(\natrec{\tup(\zero)(\varphi)}{t})(n)(a)}
   = & \compose(\snd)(\natrec{\tup(\zero)(\varphi)}{t})(\next(\zero))(a) \\
 &     \href{@functions@#def-compose}
   = & \snd(\natrec{\tup(\zero)(\varphi)}{t}(\next(\zero)))(a) \\
 &     \href{@peano@#cor-natrec-next}
   = & \snd(t(\natrec{\tup(\zero)(\varphi)}{t}(\zero)))(a) \\
 &     \href{@peano@#cor-natrec-zero}
   = & \snd(t(\tup(\zero)(\varphi)))(a) \\
 &     \let{t(\tup(n)(h)) = \tup(\next(n))(q(n)(h))}
   = & \snd(\tup(\next(\zero))(q(\zero)(\varphi)))(a) \\
 &     \href{@tuples@#thm-snd-tup}
   = & q(\zero)(\varphi)(a) \\
 &     \let{q(n)(h)(x) = \mu(n,x,h(x))}
   = & \mu(\zero,a,\varphi(a)) \\
 &     \hyp{Θ(\zero,a) = \varphi(a)}
   = & \mu(\zero,a,Θ(\zero,a))
\end{eqnarray*}$$
as claimed.

Now for the inductive step, suppose the statement holds for $n \in \nats$. Then we have

$$\begin{eqnarray*}
 &   & \natrec{\tup(\zero)(\varphi)}{t}(\next(n)) \\
 &     \href{@peano@#cor-natrec-next}
   = & t(\natrec{\tup(\zero)(\varphi)}{t}(n)) \\
 &     \hyp{\natrec{\tup(\zero)(\varphi)}{t}(n) = \tup(n)(w(n))}
   = & t(\tup(n)(w(n))) \\
 &     \let{t(\tup(n)(h)) = \tup(\next(n))(q(n)(h))}
   = & \tup(\next(n))(q(n)(w(n))) \\
 & = & (\next(n), \lambda y : \mu(n, y, Θ(n,y))) \\
 & = & (\next(n), \lambda x : Θ(\next\ n, x)).
\end{eqnarray*}$$

(Note that we used both parts of the induction hypothesis here.) Also note that

$$\begin{eqnarray*}
 &   & Θ(\next(\next(n)), a) \\
 & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\next(\next\ n))(a) \\
 & = & \snd(\natrec{(\zero, \varphi)}{t}(\next(\next\ n)))(a) \\
 & = & \snd(t(\natrec{(\zero, \varphi)}{t}(\next\ n)))(a) \\
 & = & (\snd (t (\next\ n, \lambda x : Θ(\next\ n, x))))(a) \\
 & = & (\snd (\next(\next\ n), \lambda y : \mu(\next\ n, y, Θ(\next\ n, y))))(a) \\
 & = & (\lambda y : \mu(\next\ n, y, Θ(\next\ n, y)))(a) \\
 & = & \mu(\next\ n, a, Θ(\next\ n, a))
\end{eqnarray*}$$

So $Θ$ has the claimed properties by induction. To see that $Θ$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $Θ$. Then we have $$\Psi(\zero, a) = \varphi(a) = Θ(\zero, a)$$ for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = Θ(n, a)$ for all $a \in A$, we have

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \mu(n, a, \Psi(n, a)) \\
 & = & \mu(n, a, Θ(n, a)) \\
 & = & Θ(\next\ n, a)
\end{eqnarray*}$$

for all $a \in A$. Thus $\Psi = Θ$ as needed.
::::::::::::::::::::
::::::::::::::::::::

That proof may look complicated, but structurally it's very simple. We defined $Θ$ and showed it has the claimed properties with induction, then we showed it is unique by induction.


Implementation
--------------

As we did with $\natrec{\ast}{\ast}$, we'd like to implement $\simprec{\ast}{\ast}$ in software. There are a couple of ways to go about this.

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

> simpleRec' phi mu n a =
>   let t (Pair m h) = tup (next m) (\x -> mu m x (h x))
>   in snd (naturalRec (tup zero phi) t n) $ a

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

This page is already long enough, so I'll save examples of simple recursion for another day. Just note what $\simprec{\ast}{\ast}$ does: given some data $\varphi$ and $\mu$, it produces a recursive function with signature $\nats \times A \rightarrow B$. So whenever we encounter (or want to construct) a function with this signature, it may be worthwhile to look for a definition in terms of $\simprec{\ast}{\ast}$. The uniqueness of simple recursion makes such functions very nice to reason about.

As with natural recursion, the "uniqueness" part of simple recursion is also handy. To be a little more explicit, it says the following.

:::::: corollary :::
Let $A$ and $B$ be sets, with $\varphi : \nats \times A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then $\simprec{\varphi}{\mu}$ is the unique solution $f : \nats \times A \rightarrow B$ to the following system of functional equations for all $k \in \nats$, $a \in A$, and $b \in B$:
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
> _test_simplerec n a b maxSize numCases = do
>   testLabel3 "simpleRec" n a b
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
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
