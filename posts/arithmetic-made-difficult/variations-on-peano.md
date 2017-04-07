---
title: Variations on Peano
author: nbloomf
date: 2014-05-20
tags: arithmetic-made-difficult
---

Before we get too far along, lets show that our natural numbers satisfy the remaining two traditional Peano axioms. (We established the induction principle.)

First, zero is not the successor of any natural number:

<div class="result">
<div class="thm"><p>
There is not a natural number $m$ such that $\zero = \next(m)$.
</p></div>

<div class="proof">
Suppose to the contrary that $\next(m) = \zero$. Let $\const(\bfalse)$ be the constant false map on $\bool$, and note that $(\bool, \btrue, \const(\bfalse))$ is an iterative set. Let $\Theta$ denote the unique iterative homomorphism $\natrec{\btrue}{\const(\bfalse)} : \nats \rightarrow \bool$.

We thus have $$\btrue = \Theta(\zero) = \Theta(\next(m)) = (\const(\bfalse))(\Theta(m)) = \bfalse,$$ which is absurd.
</div>
</div>

(There was nothing preventing us from giving this proof shortly after the definition of $\nats$.)

The remaining Peano axiom says that if $\next(a) = \next(b)$, then $a = b$; that is, the mapping $\next$ is injective. Before showing this, we make a definition.

<div class="result">
<div class="defn">
We let $1 = \{\ast\}$ be a set with only one element, and define $\varphi : 1 \rightarrow \nats$ and $\mu : \nats \times 1 \times \nats \rightarrow \nats$ by $$\varphi(\ast) = 0$$ and $$\mu(k,\ast,m) = k.$$ We then define $\prev : \nats \rightarrow \nats$ by $$\prev(n) = \primrec{\varphi}{\mu}(n,\ast).$$
</div>
</div>

It then follows from the properties of $\primrec{\ast}{\ast}$ that

<div class="result">
<div class="lemma"><p>
* $\prev(\zero) = \zero$
* $\prev(\next(k)) = k$ for all $k \in \nats$
</p></div>
</div>

And so

<div class="result">
<div class="thm"><p>
If $n,m \in \nats$ such that $\next(n) = \next(m)$, then $n = m$.
</p></div>
</div>
