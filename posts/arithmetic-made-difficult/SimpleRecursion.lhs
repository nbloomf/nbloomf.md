---
title: Simple Recursion
author: nbloomf
date: 2014-05-07
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module SimpleRecursion
>   ( simpleRec
>   ) where
> 
> import NaturalNumbers

So far we've defined the natural numbers as an iterative set with a special *universal property*, which was encapsulated in the existence of a simple recursion operator $\natrec{\ast}{\ast}$. Anything we will wish to do with the natural numbers can be done using this operator alone. However, in practice, it will be handy to define synonyms for some more complicated recursive functions; the first of these is *simple recursion with a parameter*.

<div class="result">
<div class="thm">
Suppose we have sets $A$ and $B$ and functions $\varphi : A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then there is a unique function $\Theta : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$\Theta(\zero, a) = \varphi(a)$$ and $$\Theta(\next(n), a) = \mu(n, a, \Theta(n, a)).$$

This function $\Theta$ will be denoted $\simprec{\varphi}{\mu}$.
</div>

<div class="proof">
First we establish existence. Define a mapping $t : \nats \times {}^AB \rightarrow \nats \times {}^AB$ by $$t(n,h) = (\next(n), \lambda x : \mu(n, x, h(x))).$$ Note that we are using the $\lambda$ notation to define an anonymous function $A \rightarrow B$ on the right hand side; specifically, $\lambda x : \mu(n, x, h(x))$ is the function $q : A \rightarrow B$ such that $q(x) = \mu(n,x,h(x))$.

Now we define $\Theta$ as follows: $$\Theta(n,a) = (\snd \circ \natrec{(\zero, \varphi)}{t})(n)(a).$$

($\snd$ is the map which selects the second entry of a pair.)

Note that $$\begin{eqnarray*}
 &   & \Theta(\zero,a) \\
 & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\zero)(a) \\
 & = & (\snd(\natrec{(\zero, \varphi)}{t})(\zero))(a) \\
 & = & (\snd(\zero, \varphi))(a) \\
 & = & \varphi(a).
\end{eqnarray*}$$

To show the second property of $\Theta$, we will show by induction that the following (compound) statement holds for all $n \in \nats$:

1. $\natrec{(\zero,\varphi)}{t}(n) = (n, \lambda x : \Theta(n,x))$ and
2. $\Theta(\next(n), a) = \mu(n, a, \Theta(n, a))$ for all $a \in A$.

For the base case, note that

$$\begin{eqnarray*}
 &   & \natrec{(\zero, \varphi)}{t}(\zero) \\
 & = & (\zero, \varphi) \\
 & = & (\zero, \lambda x : \varphi(x)) \\
 & = & (\zero, \lambda x : \Theta(\zero, x))
\end{eqnarray*}$$

and that for all $a \in A$,

$$\begin{eqnarray*}
 &   & \Theta(\next\ \zero, a) \\
 & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\next\ \zero)(a) \\
 & = & (\snd (\natrec{(\zero, \varphi)}{t}(\next\ \zero)))(a) \\
 & = & (\snd (t(\natrec{(\zero, \varphi)}{t}(\zero))))(a) \\
 & = & (\snd (t(\zero, \varphi)))(a) \\
 & = & (\snd (\next\ \zero, \lambda x : \mu(\zero, x, \varphi(x))))(a) \\
 & = & (\lambda x : \mu(\zero, x, \varphi(x)))(a) \\
 & = & \mu(\zero, a, \varphi(a)) \\
 & = & \mu(\zero, a, \Theta(\zero, a)).
\end{eqnarray*}$$

Now for the inductive step, suppose the statement holds for $n \in \nats$. Then we have

$$\begin{eqnarray*}
 &   & \natrec{(\zero, \varphi)}{t}(\next\ n) \\
 & = & t(\natrec{(\zero, \varphi)}{t}(n)) \\
 & = & t(n, \lambda x : \Theta(n,x)) \\
 & = & (\next\ n, \lambda y : \mu(n, y, \Theta(n,y))) \\
 & = & (\next\ n, \lambda x : \Theta(\next\ n, x).
\end{eqnarray*}$$

(Note that we used both parts of the induction hypothesis here.) Also note that

$$\begin{eqnarray*}
 &   & \Theta(\next(\next\ n), a) \\
 & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\next(\next\ n))(a) \\
 & = & (\snd (\natrec{(\zero, \varphi)}{t}(\next(\next\ n)))(a) \\
 & = & (\snd (t (\natrec{(\zero, \varphi)}{t}(\next\ n)))(a) \\
 & = & (\snd (t (\next\ n, \lambda x : \Theta(\next\ n, x))))(a) \\
 & = & (\snd (\next(\next\ n), \lambda y : \mu(\next\ n, y, \Theta(\next\ n, y))))(a) \\
 & = & (\lambda y : \mu(\next\ n, y, \Theta(\next\ n, y)))(a) \\
 & = & \mu(\next\ n, a, \Theta(\next\ n, a))
\end{eqnarray*}$$

So $\Theta$ has the claimed properties by induction. To see that $\Theta$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $\Theta$. Then we have $$\Psi(\zero, a) = \varphi(a) = \Theta(\zero, a)$$ for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = \Theta(n, a)$ for all $a \in A$, we have

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \mu(n, a, \Psi(n, a)) \\
 & = & \mu(n, a, \Theta(n, a)) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

for all $a \in A$. Thus $\Psi = \Theta$ as needed.
</div>
</div>

That proof may look complicated, but structurally it's very simple. We defined $\Theta$ and showed it has the claimed properties with induction, then we showed it is unique by induction.


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

> simpleRec'' phi mu n a = case natShape n of
>   Zero   -> phi a
>   Next k -> mu k a $ simpleRec'' phi mu k a

There's the definition from the proof:

> simpleRec' phi mu n a =
>   let t (m,h) = (next m, \x -> mu m x (h x))
>   in snd (naturalRec (zero,phi) t n) $ a

And the tail recursive strategy:

> simpleRec phi mu n a =
>   let
>     tau !x h m = case natShape m of
>       Zero   -> x
>       Next k -> tau (mu h a x) (next h) k
>   in tau (phi a) zero n

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
