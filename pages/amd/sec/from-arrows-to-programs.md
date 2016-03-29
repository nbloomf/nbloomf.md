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


So calling ``d7`` in ``ghci``, for instance, prints

    NNNNNNNZ

And we can also give a straightforward implementation of $\natrec{\ast}{\ast}$.


```haskell
natRec' :: a -> (a -> a) -> Nat -> a
natRec' e _    Z    = e
natRec' e phi (N n) = phi (natRec' e phi n)
```


For example:

    let theta = natRec' True not

and we can test out this map by evaluating it on several natural numbers:

    > theta d3
    False
    > theta d6
    True

Now this ``theta`` is pretty silly (though not *that* silly, it detects the parity of a natural number, which we haven't defined yet). But in the next section we'll define a more interesting recursive function.


## But...

There is a practical problem with this implementation of ``natRec'``. If we evaluate on a natural number like ``NNNZ``, the "stack" of function calls expands to something like this:

       natRec' e phi (N $ N $ N Z)
    == phi $ natRec' e phi (N $ N Z)
    == phi $ phi $ natRec' e phi (N Z)
    == phi $ phi $ phi $ natRec' e phi Z
    == phi $ phi $ phi $ e
    == phi $ phi $ e'
    == phi $ e''
    == e'''

So we generate a tower of unevaluated calls to ``phi``, $n$ tall, before collapsing it down again. In the meantime all those unevaluated ``phi``s are sitting in memory. It is not difficult to see that if we evaluate ``natRec'`` on a "larger" number (whatever that means) we will quickly run out of actual memory. To help with this, we can try rewriting ``natRec`` in so-called "tail call" recursive form like so.


```haskell
natRec :: a -> (a -> a) -> Nat -> a
natRec e phi n =
  let
    tau !x k = case k of
      Z   -> x
      N m -> tau (phi x) m
  in tau e n
```


Now ``natRec`` does not leave a bunch of unevaluated functions in memory. It is effectively a loop, iterating "up" from 0 (again with the scare quotes because we don't have an order on $\nats$ yet but of course you know what it means) rather than "down" from $n$. So this version expands to something like this:

       natRec e phi (N $ N $ N Z)
    == tau e (N $ N $ N Z)
    == tau e' (N $ N Z)
    == tau e'' (N Z)
    == tau e''' Z
    == e'''

It deconstructs its natural number argument and evaluates ``phi`` strictly at each step. (That is what the bang pattern and ``$!`` are for.) At least I think that's what it does; my simple testing shows that ``natRec'`` easily falls down while ``natRec`` does not. But profiling Haskell seems like a bit of dark art to me still. I am open to being wrong here.

We can see that ``natRec`` has better performance than ``natRec'``, but there is a hitch. ``natRec'`` is obviously an implementation of $\natrec{\ast}{\ast}$. But it is **not** obvious that ``natRec`` and ``natRec'`` are the same function! This is where the universal property of natural recursion comes in: if we can show that both functions satisfy the universal property, then *they must be the same*. And we can do this using induction.

First, we claim that for all ``n :: Nat``,

    natRec' (phi e) phi n == phi $ natRec' e phi n

Using induction, it suffices to note that

       natRec' (phi e) phi Z
    == phi e
    == phi $ natRec' e phi Z

and that if the equation holds for ``n``, then

       natRec' (phi e) phi (N n)
    == phi $ natRec' (phi e) phi n
    == phi $ phi $ natRec' e phi n
    == phi $ natRec' e phi (N n)

Now, again using induction, we have

       natRec e phi Z
    == tau e Z
    == e
    == natRec' e phi Z

and if ``natRec e phi n == natRec' e phi n``, then

       natRec e phi (N n)
    == tau e (N n)
    == tau (phi e) n
    == natRec (phi e) phi n
    == natRec' (phi e) phi n
    == phi $ natRec' e phi n
    == natRec' e phi (N n)

Since ``natRec e phi`` and ``natRec' e phi`` are both functions with signature ``Nat -> a`` which satisfy the universal property of $\nats$, they must be the same function: equal on all inputs.

This is a powerful idea. We've effectively written a slow but obviously correct program, and then proven it is equivalent to a more efficient one. We'll be doing more of this later.
