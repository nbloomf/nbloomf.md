---
title: Norm Recursion
author: nbloomf
date: 2017-12-25
tags: arithmetic-made-difficult, literate-haskell
---

> module NormRecursion where
> 
> import Prelude ()

The essence of recursion is to solve problems by combining solutions to smaller instances of the same problem. The recursion patterns we've identified so far take a specific and limited view of what "smaller instance" means; the instance smaller than $\next(n)$ is just $n$. We can think of this as the recursion embodied in the induction principle, where we prove theorems about all natural numbers by assuming they hold for $n$ and showing they also hold for $\next(n)$.

We've seen an alternative induction principle -- strong induction -- which allows us to prove theorems by assuming they hold for all $k$ with $\nleq(k,n)$ and showing they hold for $\next(n)$. Logically, strong induction is equivalent to "ordinary" induction, and so is redundant. But as we've seen, the stronger induction hypothesis of strong induction can make some proofs more convenient.

Today we'll establish a recursion pattern analogous to strong induction. 

<div class="result">
<div class="dfn"><p>
Let $(A,\varepsilon,\varphi)$ be an iterative set. A map $\eta : A \rightarrow \nats$ is called an *iterative norm* if the following hold for all $a \in A$.

1. If $\eta(a) = \zero$, then $\eta(\varphi(a)) = \zero$.
2. If $\eta(a) = \next(n)$, then $\nleq(\eta(\varphi(a)),n)$.
</p></div>
</div>

Roughly speaking, an iterative norm is a measure of "size" on $A$ with the property that this size is strictly decreasing under the action of $\varphi$.

<div class="result">
<div class="thm"><p>
Let $(A,\varepsilon,\varphi)$ be an iterative set, with $\eta : A \rightarrow \nats$ an iterative norm. Let $B$ be a set, with $\chi : A \rightarrow B$. Then there is a unique map $\Theta : A \rightarrow B$ such that, for all $a \in A$, $$\Theta(a) = \bif{\iszero(\eta(a))}{\chi(a)}{\Theta(\varphi(a))}.$$ This $\Theta$ will be denoted $\normrec{\eta}{\chi}$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>
