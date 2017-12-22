---
title: Variations on Peano
author: nbloomf
date: 2014-05-20
tags: arithmetic-made-difficult
---

The remaining Peano axiom says that if $\next(a) = \next(b)$, then $a = b$; that is, the mapping $\next$ is injective. Before showing this, we make a definition.

<div class="result">
<div class="defn">
We let $1 = \{\ast\}$ be a set with only one element, and define $\varphi : 1 \rightarrow \nats$ and $\mu : \nats \times 1 \times \nats \rightarrow \nats$ by $$\varphi(\ast) = 0$$ and $$\mu(k,\ast,m) = k.$$ We then define $\prev : \nats \rightarrow \nats$ by $$\prev(n) = \simprec{\varphi}{\mu}(n,\ast).$$
</div>
</div>

It then follows from the properties of $\simprec{\ast}{\ast}$ that

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
