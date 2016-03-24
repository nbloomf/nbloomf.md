---
title: From Arrows to Programs
author: nbloomf
---

A nice consequence of wrapping up recursion in the $\natrec{\ast}{\ast}$ function is that it allows us to write programs, independent of any implementation, and prove things about them. We'll see lots of examples of this, but first we need to establish a structural result: every natural number is either $\zero$ or of the form $\next(m)$ for some natural number $m$.

<div class="result">
<div class="lemma">
<p>If $n \in \mathbb{N}$, then either $n = \zero$ or $n = \next(m)$ for some $m$.</p>
</div>

<div class="proof">
Suppose to the contrary that there is an element $s \in \nats$, not equal to $\zero$, which is not of the form $\next(m)$ for some $m$. Note that $\bool$, with the distinguished element $\btrue$ and the constant function $\const(\btrue) : \bool \rightarrow \bool$, is an iterative set. Let $\Theta$ denote the unique iterative homomorphism $\natrec{\btrue}{\const(\btrue)} : \nats \rightarrow \bool$.

Now we define another mapping $\Psi : \nats \rightarrow \bool$ as follows: $$\Psi(x) = \left\{ \begin{array}{ll} \Theta(x) & \mathrm{if}\ x \neq s \\ \bnot(\Theta(x)) & \mathrm{if}\ x = s \end{array} \right.$$ We claim that $\Psi$ is an iterative homomorphism. To see this, note that $$\Psi(\zero) = \Theta(\zero) = \btrue$$ (since $\zero \neq s$) and that if $x \in \nats$, $$\Psi(\next(x)) = \Theta(\next(x)) = (\const\ \btrue)(\Theta(x)) = \btrue = (\const\ \btrue)(\Psi(x))$$ (since $\next(x) \neq s$). That is, $\Psi$ is an iterative homomorphism from $(\nats, \zero, \next)$ to $(\bool, \btrue, \const(\btrue))$, and since $\Theta$ is unique, we have $\Psi = \Theta$. But this implies that $\Theta(s) = \Psi(s) = \bnot(\Theta(s))$, which is absurd.
</div>
</div>

Establishing that every natural number is either $\zero$ or of the form $\next(m)$ for some $m$ justifies our use of the following Haskell type to model the natural numbers.


```haskell
data Nat
  = Z | N Nat

instance Show Nat where
  show  Z    = "Z"
  show (N k) = 'N' : show k
```


(That ``show`` instance is so we can display elements of ``Nat`` without too many parentheses.) We also define a few synonyms for "small" natural numbers as follows.


```haskell
d0 = Z
d1 = N d0
d2 = N d1
d3 = N d2
d4 = N d3
d5 = N d4
d6 = N d5
d7 = N d6
d8 = N d7
d9 = N d8
dA = N d9
dB = N dA
dC = N dB
dD = N dC
dE = N dD
dF = N dE
```


So calling ``d7`` in GHCI, for instance, prints

    NNNNNNNZ

And we can also give a straightforward implementation of $\natrec{\ast}{\ast}$.


```haskell
natRec :: a -> (a -> a) -> Nat -> a
natRec e _  Z    = e
natRec e f (N n) = f (natRec e f n)
```


For instance, the mapping we used to show that $\zero = \next(m)$ has no solution in $\nats$ is

    let theta = natRec True not

and we can test out this map by evaluating it on several natural numbers:

    > theta d3
    False
    > theta d6
    True

Now this ``theta`` is pretty silly (though not *that* silly, it detects the parity of a natural number, which we haven't defined yet). But in the next section we'll define a more interesting recursive function.
