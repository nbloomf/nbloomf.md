---
title: Strong Induction
author: nbloomf
date: 2017-04-06
tags: arithmetic-made-difficult
---

In this post we'll take a break from defining programs to establish two important equivalent versions of the induction principle: first a version of induction that allows us to make a much "stronger" induction hypothesis, and then a nonconstructive result about $\nats$ that will make some proofs easier.

<div class="result">
<div class="thm">
(Strong Induction.) Suppose we have a map $f : \nats \rightarrow A$ and a subset $B \subseteq A$ such that the following hold.

1. $f(\zero) \in B$.
2. If $f(k) \in B$ whenever $\nleq(k,n)$, then $f(\next(n)) \in B$.

Then $f(n) \in B$ for all $n \in \nats$.
</div>

<div class="proof"><p>
Let $B$ be such a subset.

Define $$T = \{ n \in \nats \mid \mathrm{if}\ \nleq(k,n)\ \mathrm{then}\ f(k) \in B \}.$$ We will show that $T = \nats$ by induction. For the base case $n = \zero$, note that if $\nleq(k,\zero)$, then $k = \zero$, and we have $f(\zero) \in B$ by condition (1).

Next suppose $n \in T$, and suppose further that $\nleq(k,\next(n))$. Now either $\nleq(k,n)$ or $k = \next(n)$. If $\nleq(k,n)$, then since $n \in T$ we have $f(k) \in B$. If $k = \next(n)$, we have $f(\next(n)) \in B$ by condition (2). Thus $\next(n) \in T$ as needed.

Now suppose $n \in \nats$. Since $\nleq(n,n)$ and $n \in T$, we have $f(n) \in B$ as claimed.
</p></div>
</div>

As with ordinary induction, we will typically apply this theorem with $A = \nats$ and $f$ the identity.

Note that condition (2) in the Strong Induction theorem appears to be much stronger than the corresponding condition in ordinary induction. Here we are allowed to assume that a given statement is true for *all* integers up to some bound $n$, while plain induction makes that assumption only for $n$. However it turns out that these two results are equivalent; in fact it's not too difficult to see that strong induction implies ordinary induction. Despite this, there are times when the stronger induction hypothesis makes for a simpler proof.

<div class="result">
<div class="thm">
(Well-Ordering Property.) Let $A$ be a nonempty set and $f : A \rightarrow \nats$. Then there exists $a \in A$ such that $\nleq(f(a),f(b))$ for all $b \in A$.
</div>

<div class="proof"><p>
Suppose to the contrary that some set $A$ and map $f : A \rightarrow \nats$ exist which do not have this property; that is, for all $a \in A$, there exists $b \in A$ such that $\nleq(f(a),f(b))$ is false.

Define $$T = \{ n \in \nats \mid \exists a \in A, n = f(a) \},$$ and let $K = \nats \minus T$. Note that $T \neq \emptyset$. We will show that $K = \nats$ by strong induction.

For the base case, note that if $f(a) = \zero$, then $\nleq(f(a),f(b))$ is true for all $b \in A$. So we have $\zero \notin T$, and thus $\zero \in K$.

For the inductive step, suppose we have $n \in \nats$ such that $k \in K$ whenever $\nleq(k,n)$. Now suppose that $\next(n) \notin K$, that is, $\next(n) \in T$; say $\next(n) = f(a)$. Now suppose we have $b \in A$. If $\nleq(f(a),f(b))$ is false, then $\nleq(f(b),f(a))$ is true and $f(b) \neq \next(n)$. But now $\nleq(f(b),n)$, so that $f(b) \in K$, a contradiction. Thus we have $\nleq(f(a),f(b)) = \btrue$ for all $b$, a contradiction. So in fact $\next(n) \in K$.

By induction, then, we have $K = \nats$, so that $T = \emptyset$, a contradiction. So in fact no such $A$ and $f$ can exist.
</p></div>
</div>

Again, in typical applications we will have $A = \nats$ and $f$ the identity.
