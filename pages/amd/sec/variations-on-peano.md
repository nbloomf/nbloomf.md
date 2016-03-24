---
title: Variations on Peano
author: nbloomf
---

As an example, lets show that our natural numbers satisfy the more traditional Peano axioms.

First, zero is not the successor of any natural number:

<div class="result">
<div class="lemma">
<p>There is not a natural number $m$ such that $\zero = \next(m)$.</p>
</div>

<div class="proof">
Suppose to the contrary that $\next(m) = \zero$. Let $\const(\bfalse)$ be the constant false map on $\bool$, and note that $(\bool, \btrue, \const(\bfalse))$ is an iterative set. Let $\Theta$ denote the unique iterative homomorphism $\natrec{\btrue}{\const(\bfalse)} : \nats \rightarrow \bool$.

We thus have $$\btrue = \Theta(\zero) = \Theta(\next(m)) = (\const(\bfalse))(\Theta(m)) = \bfalse,$$ which is absurd.
</div>
</div>

And the induction principle:

<div class="result">
<div class="lemma">
Suppose $f : \nats \rightarrow A$ is a map and that $B \subseteq A$ is a subset such that $f(\zero) \in B$ and whenever $f(n) \in B$, we also have $f(\next(n)) \in B$. Then in fact $f(n) \in B$ for all natural numbers $n$.
</div>

<div class="proof">
Define a subset $T \subseteq \nats$ by $$T = \{n \in \nats \mid f(n) \in B \}.$$ By hypothesis, we have $\zero \in T$. Also, if $n \in T$, then $\next(n) \in T$; in particular, the restriction of $\next$ to $T$ is in fact a function $T \rightarrow T$. That is, $(T,\zero,\next)$ is an iterative set. Let $\Theta = \natrec{\zero}{\next}$ be the unique homomorphism $\nats \rightarrow T$.

Now let $\iota : T \rightarrow \nats$ denote the inclusion map; in fact $\iota$ is an iterative homomorphism, since we have $\iota(\zero) = \zero$ and $$\iota(\next(n)) = \next(n) = \next(\iota(n))$$ for all $n \in T$.

The composite map $\iota \circ \Theta : \nats \rightarrow \nats$ is again an iterative homomorphism, and by uniqueness, in fact we have $\iota \circ \Theta = \id$. If $n$ is a natural number, we have $$n = \id(n) = \iota(\Theta(n)) = \Theta(n),$$ and in particular, $n \in T$. That is, if $n$ is any natural number, we have $f(n) \in B$.
</div>
</div>
