---
author: nbloomf
date: 2010-12-21
category: D&F
title: A domain which is not atomic
tags: ring, domain, atomic domain, example, irreducible
---

Let $R = \mathbb{Z} + x\mathbb{Q}[x] \subseteq \mathbb{Q}[x]$ be the set of all rational polynomials whose constant term is an integer.

  1. Prove that $R$ is an integral domain and that the units in $R$ are $\pm 1$.
  2. Show that the irreducible elements in $R$ are $\pm p$ for prime integers $p$ and the irreducible polynomials $p(x) \in \mathbb{Q}[x]$ whose constant coefficient is $\pm 1$.
  3. Show that $x \in R$ cannot be written as a product of irreducibles. and conclude that $R$ is not a unique factorization domain.
  4. Show that $x \in R$ is not prime and describe the quotient $R/(x)$.

* * *

  1. As a subring of the integral domain $\mathbb{Q}[x]$, $R$ must also be an integral domain. Now suppose $ab = 1$ with $a, b \in R$. Computing the degrees of both sides we see that $a$ and $b$ are constants, and thus integers. So $a, b = \pm 1$ as claimed.

  2. Let $p(x) \in R$ be irreducible. If $p(x)$ has degree $0$ then $p$ is an integer. Now if $p = ab$, then considering degrees both $a$ and $b$ are integers and without loss of generality $a = \pm 1$. Thus $p$ is an irreducible -- hence prime -- integer. Suppose now that $p(x)$ has positive degree. Suppose further that $p(x) \in \mathbb{Q}[x]$ is reducible; say $p = ab$ where $a, b \in \mathbb{Q}[x]$. We may also write $p(x) = qp^\prime(x)$, where $q \in \mathbb{Q}$ and $p^\prime(x) \in \mathbb{Z}[x]$. Then $p^\prime = q^{-1}a(x)b(x)$ is reducible in $\mathbb{Q}[x]$. By Gauss' Lemma, $p^\prime = a^\prime(x)b^\prime(x)$, with $a^\prime,b^\prime \in \mathbb{Z}[x]$. Then $p(x) = qa^\prime(x)b^\prime(x)$. In particular, the constant coefficient $qa_0b_0$ is an integer, where $a_0$ and $b_0$ are integers and $q$ is rational. Suppose $q$ is given in lowest terms and write the denominator of $q$ as $q_aq_b$, where $q_a|a_0$ and $q_b|b_0$. Let $q_n$ be the numerator of $q$. Then $p(x) = (\frac{q_n}{q_a}a(x))(\frac{1}{q_b}b(x))$ is a factorization of $p(x)$ in $R$, and thus $p(x) \in R$ is reducible - a contradiction. So $p(x) \in \mathbb{Q}[x]$ must be irreducible. Now write $p(x) = a + xp^\prime(x)$. If $|a| \neq 1$, then there exists a prime integer $q$ dividing $a$; say $a = qb$. Then $p(x) = q(b + \frac{1}{q}xp^\prime(x))$. Neither of these factors is a unit, so that $p(x)$ is not irreducible after all - a contradiction. Thus $|a| = 1$ as desired.

  3. Suppose $x = \prod a_i$ is a product of irreducibles $a_i$. Since the degree of a product is the sum of degrees, exactly one of the $a_i$ is linear - say $a_0$ - and the rest are constants. By part (2), $a_0 = ax \pm 1$. But then $\prod a_i$ has a nonzero constant term, a contradiction. Thus $x$ cannot be written as a product of irreducibles in $R$.

  4. Now we show that $x \in R$ is not prime. Note that $2 \cdot \frac{1}{2}x = x$, and both of these factors is in $R$. However, $2$ is not divisible by $x$ (computing degrees). Suppose $\frac{1}{2}x \in (x)$. Then $\frac{1}{2}x = ax$, and since $R$ is an integral domain, $a = \frac{1}{2} \in R$, a contradiction. So $x$ is not prime in $R$.

We claim that $R/(x) = \{ a + bx + (x) \mid a \in \mathbb{Z}, b \in \mathbb{Q}, 0 \leq b < 1 \}$. The $(\supseteq)$ direction is clear. To see $(\subseteq)$, suppose $p(x) + (x) \in R/(x)$ with $p(x) = \sum a_i x^i$. All powers of $x$ of exponent at least 2 are in $(x)$. Moreover, if $a_1x$ is the linear coefficient of $p(x)$, we can write $a_1x = a_1^\prime x + kx$ where $k \in \mathbb{Z}$ and $a_1^\prime$ is in the interval $[0,1)$. Since $kx \in (x)$, we have $p(x) + (x) = a_0 + a_1^\prime x + (x)$, as desired. Next we show that these representatives give distinct cosets. Suppose $a_1 + b_1x + (x) = a_2 + b_2x + (x)$; then $(a_1 - a_2) + (b_1 - b_2)x \in (x)$. Since every element of $(x)$ has zero constant term, $a_1 = a_2$. Now $(b_1 - b_2)x \in (x)$, so that $(b_1 - b_2)x = q(x)x$. Computing degrees, in fact $q$ is constant and we have $b_1 - b_2 \in \mathbb{Z}$. Thus $b_1 - b_2 = 0$, so that $b_1 = b_2$.


