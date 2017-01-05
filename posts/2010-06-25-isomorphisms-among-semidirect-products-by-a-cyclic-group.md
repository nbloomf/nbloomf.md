---
title: Isomorphisms among semidirect products by a cyclic group
author: nbloomf
date: 2010-06-25
tags: cyclic-group, isomorphism, semidirect-product, d-and-f
---

Let $K$ be a cyclic group, $H$ an arbitrary group, and $\alpha$ and $\beta$ homomorphisms $K \rightarrow \mathsf{Aut}(H)$. If $K$ is infinite, suppose further that $\alpha$ and $\beta$ are injective.

Show that if $\mathsf{im}\ \alpha$ and $\mathsf{im}\ \beta$ are conjugate subgroups in $\mathsf{Aut}(H)$, then $$H \rtimes_{\alpha} K \cong H \rtimes_{\beta} K.$$

* * *

Let $x$ be a generator of $K$ and say that $\sigma$ conjugates $\mathsf{im}\ \alpha$ into $\mathsf{im}\ \beta$; that is, that $\sigma\left(\mathsf{im}\ \alpha\right)\sigma^{-1} = \mathsf{im}\ \beta$.

In particular, $\sigma \alpha(x) \sigma^{-1} \in \mathsf{im}\ \beta$, so that $\sigma \alpha(x) \sigma^{-1} = \beta(x^a)$ for some (not necessarily unique!) $x^a \in K$. Now if $x^b$ is any element of $K$, we have $$\sigma \alpha(x^b) \sigma^{-1} = \sigma \alpha(x)^b \sigma^{-1} = \left(\sigma \alpha(x) \sigma^{-1}\right)^b = \beta(x)^{ab} = \beta(x^b)^a.$$ In particular, for all $k \in K$ we have $\sigma \alpha(k) = \beta(k)^a \sigma$.

Now define a mapping $\psi : H \rtimes_{\alpha} K \rightarrow H \rtimes_{\beta} K$ by $\psi(h,k) = (\sigma(h), k^a)$. We claim that $\psi$ is a group homomorphism.

To see this, let $(h_1,k_1), (h_2,k_2) \in H \rtimes_{\varphi\_1} K$. We have
$$\begin{array}{rcl}
\psi\left((h_1,k_1) \cdot (h_2,k_2)\right)
 & = & \psi\left(h_1 \alpha(k_1)(h_2), k_1k_2\right) \\
 & = & \left(\sigma(h_1 \alpha(k_1)(h_2)), (k_1k_2)^a\right) \\
 & = & \left(\sigma(h_1) \sigma(\alpha(k_1)(h_2)), k_1^a k_2^a\right) \\
 & = & \left(\sigma(h_1) (\sigma \circ \alpha(k_1))(h_2), k_1^a k_2^a\right) \\
 & = & \left(\sigma(h_1) (\beta(k_1)^a \sigma)(h_2), k_1^a k_2^a\right) \\
 & = & \left(\sigma(h_1) \beta(k_1^a)(\sigma(h_2)), k_1^a k_2^a\right) \\
 & = & \left(\sigma(h_1), k_1^a)(\sigma(h_2), k_ 2^a\right) \\
 & = & \psi(h_1,k_1) \cdot \psi(h_2,k_2), \\
\end{array}$$
and thus $\psi$ is a homomorphism.

We now show that $\psi$ is bijective.

First suppose $K$ is infinite, so that (by hypothesis) both $\alpha$ and $\beta$ are injective. Just as $\sigma \alpha(k) = \beta(k)^a \sigma$ for all $k \in K$, there is an integer $b$ such that $\beta(k) \sigma = \sigma \alpha(k)^b$ for all $k \in K$. Combining these results we see that $\beta(k) = \beta(k^{ab})$. Since $\beta$ is injective we have $k^{1-ab} = 1$, and since $K$ is infinite and $k$ arbitrary, we have $ab = 1$. Thus $a = b \in \{1,-1\}$; in either case we have $a^2 = 1$.

Define a mapping $\chi : H \rtimes_{\beta} K \rightarrow H \rtimes_{\alpha} K$ by $\chi(h,k) = \left(\sigma^{-1}(h), k^a\right)$. Then $$(\chi \circ \psi)(h,k) = \chi(\psi(h,k)) = \chi(\sigma(h), k^a) = ((\sigma^{-1}\sigma)(h), k^{aa}) = (h,k),$$ so that $\chi \circ \psi = 1$. Similarly $\psi \circ \chi = 1$. Thus $\psi$ is bijective and we have $H \rtimes_{\beta} K \cong H \rtimes_{\alpha} K$.

Before proceeding to the finite case we prove the following lemma, due to [Luís Finotti](http://www.math.utk.edu/~finotti/f07/m551/M551.html).

<div class="result">
<div class="lemma">
<p>Let $a$, $m$, and $n$ be integers such that $m \mid n$ and $\mathsf{gcd}(a,m) = 1$. Then there is an integer $\overline{a}$ such that $\overline{a} \equiv a \pmod{m}$ and $\mathsf{gcd}(\overline{a},n) = 1$.</p>
</div>

<div class="proof">
Let $d = \mathsf{gcd}(a,n)$ and write $n = mq$. Note that $\mathsf{gcd}(d,m) = 1$ since $d$ divides $a$, so that $d \mid q$ by Euclid's Lemma. Write $a = a^\prime d$ and $q = q^\prime d$, and let $t$ be the (possibly empty) product of all prime divisors of $q^\prime$ which do not divide $d$. Finally, let $\overline{a} = a + tm$. Certainly $\overline{a} \equiv a \pmod{m}$.

Suppose $p$ is a prime divisor of $n$. We claim that $p$ does not divide $\overline{a}$; to show this we consider three possibilities.

1. If $p \mid m$, then $p \not\mid a$ since $a$ and $m$ are relatively prime. Thus $p$ cannot divide $a + tm = \overline{a}$.
2. If $p \not\mid m$ and $p \mid q^\prime$, we have two cases.
    1. If $p \mid d$, then $p \mid a$. We also have $p \not\mid t$ by construction, so that $p \not\mid tm$. Thus $p$ cannot divide $a + tm = \overline{a}$.
    2. If $p \not\mid d$, then $p \mid t$ by construction. Note also that $p \not\mid a$, since otherwise $p$ divides both $a$ and $n$ and so must divide $d$. Thus $p$ cannot divide $a + tm = \overline{a}$.
3. If $p \not\mid m$ and $p \not\mid q^\prime$, then since $n = m q^\prime d$ we have that $p \mid d$ and thus $p \mid a$. Now $p \not\mid t$ by construction, so that $p \not\mid tm$. Thus $p$ cannot divide $a + tm = \overline{a}$.

Since no prime divisor of $n$ divides $\overline{a}$ we have $\mathsf{gcd}(\overline{a},n) = 1$.
</div>
</div>

Now to the main result.

Suppose $K \cong Z_n$ is finite. Note that $\mathsf{im}\ \alpha$ is cyclic of order $m$ for some $m \mid n$ by Lagrange's Theorem. Since $x$ generates $K$, $\alpha(x)$ generates $\mathsf{im}\ \alpha$, and since conjugation by $\sigma$ is an isomorphism $\mathsf{im}\ \alpha \rightarrow \mathsf{im}\ \beta$, we have that $\sigma\alpha(x)\sigma^{-1} = \beta(x)^a$ generates $\mathsf{im}\ \beta$. Thus $\mathsf{gcd}(a,m) = 1$. By the lemma, there exists $\overline{a}$ such that $\overline{a} \equiv a \pmod{m}$ and $\mathsf{gcd}(\overline{a},n) = 1$. Moreover, there exists $b$ such that $\overline{a}b \equiv 1 \pmod{n}$. 

Define a map $\chi : H \rtimes_{\beta} K \rightarrow H \rtimes_{\alpha} K$ by $\chi(h,k) = (\sigma^{-1}(h), k^b)$. It is straightforward to check that this map is a two-sided inverse of $\psi$; hence $H \rtimes_{\beta} K \cong H \rtimes_{\alpha} K$.
