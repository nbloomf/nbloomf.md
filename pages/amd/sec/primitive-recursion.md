---
title: Primitive Recursion
author: nbloomf
---

So far we've defined the natural numbers as an iterative set with a special *universal property*, which was encapsulated in the existence of a simple recursion operator $\natrec{\ast}{\ast}$. Anything we will wish to do with the natural numbers can be done using this operator alone. However, in practice, it will be handy to define synonyms for some more complicated recursive functions; the first of these is *primitive recursion with a parameter*.

<div class="result">
<div class="thm">
Suppose we have sets $A$ and $B$ and functions $\varphi : A \rightarrow B$ and $\mu : \nats \times A \times B \rightarrow B$. Then there is a unique function $\Theta : \nats \times A \rightarrow B$ such that, for all $n \in \nats$ and $a \in A$, $$\Theta(\zero, a) = \varphi(a)$$ and $$\Theta(\next(n), a) = \mu(n, a, \Theta(n, a)).$$

This function $\Theta$ will be denoted $\primrec{\varphi}{\mu}$.
</div>

<div class="proof">
First we establish existence. Define a mapping $t : \nats \times {}^AB \rightarrow \nats \times {}^AB$ by $$t(n,h) = (\next(n), \lambda x : \mu(n, x, h(x))).$$ Note that we are using the $\lambda$ notation to define an anonymous function $A \rightarrow B$ on the right hand side; specifically, $\lambda x : \mu(n, x, h(x))$ is the function $q : A \rightarrow B$ such that $q(x) = \mu(n,x,h(x))$.

Now we define $\Theta$ as follows: $$\Theta(n,a) = (\snd \circ \natrec{(\zero, \varphi)}{t})(n)(a).$$

($\snd$ is the map which selects the second entry of a pair.)

Note that $$\begin{eqnarray*}
\Theta(\zero,a) & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\zero)(a) \\
 & = & (\snd(\natrec{(\zero, \varphi)}{t})(\zero))(a) \\
 & = & (\snd(\zero, \varphi))(a) \\
 & = & \varphi(a).
\end{eqnarray*}$$

To show the second property of $\Theta$, we will show by induction that the following (compound) statement holds for all $n \in \nats$:

1. $\natrec{(\zero,\varphi)}{t}(n) = (n, \lambda x : \Theta(n,x))$ and
2. $\Theta(\next(n), a) = \mu(n, a, \Theta(n, a))$ for all $a \in A$.

For the base case, note that

$$\begin{eqnarray*}
\natrec{(\zero, \varphi)}{t}(\zero) & = & (\zero, \varphi) \\
 & = & (\zero, \lambda x : \varphi(x)) \\
 & = & (\zero, \lambda x : \Theta(\zero, x))
\end{eqnarray*}$$

and that for all $a \in A$,

$$\begin{eqnarray*}
\Theta(\next\ \zero, a) & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\next\ \zero)(a) \\
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
\natrec{(\zero, \varphi)}{t}(\next\ n) & = & t(\natrec{(\zero, \varphi)}{t}(n)) \\
 & = & t(n, \lambda x : \Theta(n,x)) \\
 & = & (\next\ n, \lambda y : \mu(n, y, \Theta(n,y))) \\
 & = & (\next\ n, \lambda x : \Theta(\next\ n, x).
\end{eqnarray*}$$

(Note that we used both parts of the induction hypothesis here.) Also note that

$$\begin{eqnarray*}
\Theta(\next(\next\ n), a) & = & (\snd \circ \natrec{(\zero, \varphi)}{t})(\next(\next\ n))(a) \\
 & = & (\snd (\natrec{(\zero, \varphi)}{t}(\next(\next\ n)))(a) \\
 & = & (\snd (t (\natrec{(\zero, \varphi)}{t}(\next\ n)))(a) \\
 & = & (\snd (t (\next\ n, \lambda x : \Theta(\next\ n, x))))(a) \\
 & = & (\snd (\next(\next\ n), \lambda y : \mu(\next\ n, y, \Theta(\next\ n, y))))(a) \\
 & = & (\lambda y : \mu(\next\ n, y, \Theta(\next\ n, y)))(a) \\
 & = & \mu(\next\ n, a, \Theta(\next\ n, a))
\end{eqnarray*}$$

So $\Theta$ has the claimed properties by induction. To see that $\Theta$ is unique, we again use induction. Suppose $\Psi : \nats \times A \rightarrow B$ is another mapping which satisfies the properties of $\Theta$. Then we have $$\Psi(\zero, a) = \varphi(a) = \Theta(\zero, a)$$ for all $a \in A$, and if $n \in \nats$ such that $\Psi(n, a) = \Theta(n, a)$ for all $a \in A$, we have

$$\begin{eqnarray*}
\Psi(\next\ n, a) & = & \mu(n, a, \Psi(n, a)) \\
 & = & \mu(n, a, \Theta(n, a)) \\
 & = & \Theta(\next\ n, a)
\end{eqnarray*}$$

for all $a \in A$. Thus $\Psi = \Theta$ as needed.
</div>
</div>

That proof may look complicated, but structurally it's very simple. We defined $\Theta$ and showed it has the claimed properties with induction, then we showed it is unique by induction.

## Implementation

As we did with $\natrec{\ast}{\ast}$, we'd like to implement $\primrec{\ast}{\ast}$ in software. There are a couple of ways to go about this.

There's the naive way:


```haskell
primRec'' :: (a -> b) -> (Nat -> a -> b -> b) -> Nat -> a -> b
primRec'' phi _   Z    a = phi a
primRec'' phi mu (N n) a = mu n a $ primRec'' phi mu n a
```


There's the definition from the proof:


```haskell
primRec' :: (a -> b) -> (Nat -> a -> b -> b) -> Nat -> a -> b
primRec' phi mu n a =
  let t (m,h) = (N m, \x -> mu m x (h x))
  in snd (natRec (Z,phi) t n) $ a
```


And the tail recursive strategy:


```haskell
primRec :: (a -> b) -> (Nat -> a -> b -> b) -> Nat -> a -> b
primRec phi mu n a =
  let
    tau !x h m = case m of
      Z   -> x
      N k -> tau (mu h a x) (N h) k
  in tau (phi a) Z n
```


Some simple testing again shows that the tail recursive form is more efficient -- both of the other forms run out of space on medium-sized numbers. All we need to do is verify that the efficient ``primRec`` is equivalent to the inefficient, but obviously correct, ``primRec''``.

First we claim that

       primRec'' (\x -> mu k x (phi x)) mu k a
    == mu k a $ primRec'' phi mu k a

for all ``k :: Nat`` and all ``a :: a``. Using induction, note that

       primRec'' (\x -> mu Z x (phi x)) mu Z a
    == (\x -> mu Z x (phi x)) a
    == mu Z a (phi a)
    == mu Z a $ primRec'' phi mu Z a

and if the equation holds for ``k :: Nat``, then

       primRec'' (\x -> mu (N k) x (phi x)) mu (N k) a
    == mu k a $ primRec'' (\x -> mu (N k) x (phi x)) mu k a
