---
title: Primitive Recursion
author: nbloomf
date: 2014-05-23
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE BangPatterns #-}
> module PrimitiveRecursion
>   ( primitiveRec
>   ) where
> 
> import NaturalNumbers

So far we have defined two special *recursion operators*, $\natrec{\ast}{\ast}$ and $\simprec{\ast}{\ast}$. These act like program skeletons: fill in the slots with functions of the right signatures and get a computable function out. In this post we'll define one more, a much beefier generalization of simple recursion called *primitive recursion*.

<div class="result">
<div class="thm">
Suppose we have sets $A$ and $B$ and functions with the following signatures: $$\begin{eqnarray*} \varphi & : & A \rightarrow B \\ \beta & : & \nats \times A \rightarrow \bool \\ \psi & : & \nats \times A \rightarrow B \\ \omega & : & \nats \times A \rightarrow A \\ \mu & : & \nats \times A \times B \rightarrow B. \end{eqnarray*}$$ Then there is a unique function $\Theta : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$\Theta(\zero, a) = \varphi(a)$$ and $$\Theta(\next(m), a) = \left\{ \begin{array}{ll} \psi(m,a) & \mathrm{if}\ \beta(m,a) \\ \mu(m, a, \Theta(m, \omega(m,a))) & \mathrm{otherwise}. \end{array} \right.$$

This function $\Theta$ will be denoted $\primrec{\varphi}{\beta}{\psi}{\omega}{\mu}$.
</div>

<div class="proof">
This proof will be very similar to the analogous proof for simple recursion.

First we establish existence. To this end, define a map $W : \nats \times {}^AB \rightarrow {}^AB$ by $$W(m,h)(x) = \left\{ \begin{array}{ll} \psi(m,x) & \mathrm{if}\ \beta(m,x) \\ \mu(m,x,h(\omega(m,x))) & \mathrm{otherwise}, \end{array} \right.$$ and define $t : \nats \times {}^AB \rightarrow \nats \times {}^AB$ by $$t(m,h) = (\next(m), W(m,h)).$$

Now we define $\Theta$ as follows: $$\Theta(m,a) = \snd((\natrec{(\zero, \varphi)}{t})(m))(a).$$

($\snd$ is the map which selects the second entry of a pair.)

Note that
$$\begin{eqnarray*}
 &   & \Theta(\zero,a) \\
 & = & (\snd(\natrec{(\zero, \varphi)}{t})(\zero))(a) \\
 & = & (\snd(\zero, \varphi))(a) \\
 & = & \varphi(a).
\end{eqnarray*}$$

To show the second property of $\Theta$, we will show by induction that the following (compound) statement holds for all $n \in \nats$:

1. $\natrec{(\zero,\varphi)}{t}(n) = (n, \lambda x: \Theta(n,x))$ and
2. $\Theta(\next(n), a) = W(n,\lambda x: \Theta(n,x))(a)$ for all $a \in A$.

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
 & = & (\snd (\natrec{(\zero, \varphi)}{t}(\next\ \zero)))(a) \\
 & = & (\snd (t(\natrec{(\zero, \varphi)}{t}(\zero))))(a) \\
 & = & (\snd (t(\zero, \varphi)))(a) \\
 & = & (\snd (\next\ \zero, W(\zero, \varphi)))(a). \\
 & = & W(\zero, \varphi)(a). \\
 & = & W(\zero, \lambda x: \varphi(x))(a). \\
 & = & W(\zero, \lambda x: \Theta(\zero,x))(a). \\
\end{eqnarray*}$$

Now for the inductive step, suppose the statement holds for $n \in \nats$. Then we have

$$\begin{eqnarray*}
 &   & \natrec{(\zero, \varphi)}{t}(\next\ n) \\
 & = & t(\natrec{(\zero, \varphi)}{t}(n)) \\
 & = & t(n, \lambda x : \Theta(n,x)) \\
 & = & (\next\ n, W(n, \lambda x : \Theta(n,x))) \\
 & = & (\next\ n, \lambda y : W(n, \lambda x : \Theta(n,x))(y)) \\
 & = & (\next\ n, \lambda y : \Theta(\next\ n, y)
\end{eqnarray*}$$

(Note that we used both parts of the induction hypothesis here.) Also note that
$$\begin{eqnarray*}
 &   & \Theta(\next(\next\ n), a) \\
 & = & \snd (\natrec{(\zero, \varphi)}{t}(\next(\next\ n)))(a) \\
 & = & \snd (t (\natrec{(\zero, \varphi)}{t}(\next\ n)))(a) \\
 & = & \snd (t (\next\ n, \lambda x : \Theta(\next\ n, x)))(a) \\
 & = & \snd (\next(\next\ n), W(\next\ n, \lambda x : \Theta(\next\ n,x)))(a) \\
 & = & W(\next\ n, \lambda x : \Theta(\next\ n, x))(a).
\end{eqnarray*}$$

So $\Theta$ has the claimed properties by induction. To see that $\Theta$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $\Theta$. Then we have $$\Psi(\zero, a) = \varphi(a) = \Theta(\zero, a)$$ for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = \Theta(n, a)$ for all $a \in A$, we have

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \psi(n,a) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

if $\beta(n,a) = \btrue$, and

$$\begin{eqnarray*}
 &   & \Psi(\next\ n, a) \\
 & = & \mu(n, a, \Psi(n, \omega(n,a))) \\
 & = & \mu(n, a, \Theta(n, \omega(n,a))) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

if not, for all $a \in A$. Thus $\Psi = \Theta$ as needed.
</div>
</div>


Implementation
--------------

As we did with $\natrec{\ast}{\ast}$ and $\simprec{\ast}{\ast}$, we'd like to implement $\primrec{\ast}{\ast}{\ast}{\ast}{\ast}$ in software. There are a couple of ways to go about this. First, the signature.

> primRec'', primRec', primitiveRec
>   :: (Natural t)
>   => (a -> b)
>   -> (t -> a -> Bool)
>   -> (t -> a -> b)
>   -> (t -> a -> a)
>   -> (t -> a -> b -> b)
>   -> t
>   -> a
>   -> b

There's the naive way:

> primRec'' phi beta psi omega mu n a =
>   case shapeOf n of
>     Zero -> phi a
>
>     Next m ->
>       if beta m a
>         then psi m a
>         else mu m a (primRec'' phi beta psi omega mu m (omega m a))

There's the definition from the proof:

> primRec' phi beta psi omega mu = \n a ->
>   let
>     w m h x =
>       if beta m x
>         then psi m x
>         else mu m x (h $ omega m x)
> 
>     t (m,h) = (next m, w m h)

>   in snd (naturalRec (zero, phi) t n) $ a

And the tail recursive strategy:

> primitiveRec phi beta psi omega mu = \n a ->
>   let
>     tau !x !y h m = case shapeOf m of
>       Zero   -> x
>       Next k -> if beta k y
>         then psi k y
>         else tau (mu h y x) (omega k y) (next h) k
> 
>   in tau (phi a) (omega zero a) zero n

Once again we will verify that the efficient but not-obviously-correct ``primRec`` is equivalent to the inefficient but obviously correct ``primRec''``. We will (eventually) do this by induction on the ``Nat`` type.

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

    primRec phi' mu' k a == primRec phi mu (N k) a

for all ``phi``, ``mu``, ``k``, and ``a``. To see this, note that

       primRec phi mu (N k) a
    == tau (phi a) Z (N k)
    == tau (mu Z a (phi a)) (N Z) k
    == tau' (mu Z a (phi a)) Z k
    == tau' (phi' a) Z k
    == primRec phi' mu' k a

as needed. Also, ``primRec''`` satisfies this equation, which we show by induction on ``k``. For the base case, note that

       primRec'' phi' mu' Z a
    == phi' a
    == mu Z a (phi a)
    == mu Z a $ primRec'' phi mu Z a
    == primRec'' phi mu (N Z) a

And if the equation holds for ``k``, then we have

       primRec'' phi' mu' (N k) a
    == mu' k a $ primRec'' phi' mu' k a
    == mu' k a $ primRec'' phi mu (N k) a
    == mu (N k) a $ primRec'' phi mu (N k) a
    == primRec'' phi mu (N $ N k) a

so that

    primRec'' phi' mu' k a == primRec'' phi mu (N k) a

for all ``phi``, ``mu``, ``k``, and ``a`` as claimed.

Finally we are prepared to show that ``primRec == primRec''``, by induction on ``k``. For the base case, we have

       primRec'' phi mu Z a
    == phi a
    == tau (phi a) Z Z
    == primRec phi mu Z a

And if the result holds for ``k``, we have

       primRec'' phi mu (N k) a
    == primRec'' phi' mu' k a
    == primRec phi' mu' k a
    == primRec phi mu (N k) a

So our efficient ``primRec`` is equivalent to ``primRec''``. (We will leave the equivalence of ``primRec'`` and ``primRec`` as an exercise.)


What it does
------------

Note that simple recursion is a special case of primitive recursion, where $\beta$ is always false, $\omega$ is the identity function in the second argument, and $\psi$ is any map (that never gets evaluated). So why introduce simple and primitive recursion separately? Simple recursion is, well, simpler, and is plenty powerful for many purposes. So for those cases where the extra complexity of primitive recursion is not needed, it may be easier to reason with simple recursion.

However, primitive recursion does some cool things that simple recursion does not. The $\omega$ map lets us "mutate" the initial parameter $a$ at each step in the recursion, and the boolean-valued function $\beta$ lets us short-circuit a recursive function.
