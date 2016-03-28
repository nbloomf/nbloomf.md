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

