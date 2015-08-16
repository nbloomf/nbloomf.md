---
title: A lifting property for finite abelian groups
author: nbloomf
date: 2010-06-17
categories: D&F
tags: abelian-group, finite-group, homomorphism, group-presentation, generating-set
---

Let $A$ be the finite abelian group $$A = \mathbb{Z}/(n_1) \times \mathbb{Z}/(n_2) \times \cdots \times \mathbb{Z}/(n_t).$$

If $G$ is a group containing elements $g_1, g_2, \ldots, g_t$ such that $g_i^{n_i} = 1$ for each $i$ and $g_ig_j = g_jg_i$ for all $i$ and $j$, then there is a unique group homomorphism $\theta : A \rightarrow G$ such that $\theta(1_i) = g_i$ for each $i$. (Here, $1_i$ is the element of $A$ with a $\underline{1}$ in the $i$th entry and $\underline{0}$ elsewhere.)

* * *

Let $\theta \subseteq A \times G$ consist of the pairs $$\left(\left(\underline{b_i}\right)_{i=1}^t, \prod_{i=1}^t g_i^{b_i}\right).$$ We claim that $\theta$ is a group homomorphism. Clearly $\theta$ is total.

To see that $\theta$ is well-defined, suppose we have tuples $\left(\underline{b_i}\right), \left(\underline{c_i}\right) \in A$ such that $(\underline{b_i}) = (\underline{c_i})$; that is, for each $i$ we have $b_i \equiv c_i \pmod{n_i}$, and thus $b_i - c_i = k_in_i$ for some $k_i$. Now $$\prod_{i=1}^t g_i^{b_i - c_i} = \prod_{i=1}^t g_i^{k_in_i} = \prod_{i=1}^t (g_i^{n_i})^{k_i} = \prod_{i=1}^t 1^{k_i} = \prod_{i=1}^t 1 = 1,$$ and thus (since the $g_i$ commute pairwise) $$\prod_{i=1}^t g_i^{b_i} = \prod_{i=1}^t g_i^{c_i}.$$ Thus $\theta$ is a mapping.

Now note that if $\left(\underline{b_i}\right), \left(\underline{c_i}\right) \in A$, we have 
$$\begin{array}{rcl} 
\theta\left(\left(\underline{b_i}\right)+\left(\underline{c_i}\right)\right) 
 & = & \theta\left(\underline{b_i+c_i}\right) \\
 & = & \prod_{i=1}^t g_i^{b_i + c_i} \\
 & = & \prod_{i=1}^t g_i^{b_i} g_i^{c_i} \\
 & = & \prod_{i=1}^t g_i^{b_i} \cdot \prod_{i=1}^t g_i^{c_i} \\
 & = & \theta\left(\underline{b_i}\right) \cdot \theta\left(\underline{c_i}\right). \\
\end{array}$$

(From line 3 to 4 we use the fact that the $g_i$ commute pairwise.) So $\theta$ is a group homomorphism. Finally, it is clear that $\theta(1_i) = g_i$ for each $i$.

Now suppose $\sigma : A \rightarrow G$ is a group homomorphism such that $\sigma(1_i) = g_i$ for each $i$. We have
$$\begin{array}{rcl}
\sigma\left(\underline{b_i}\right)
 & = & \sigma\left(\sum_{i=1}^t b_i 1_i\right) \\
 & = & \prod_{i=1}^t \sigma(1_i)^{b_i} \\
 & = & \prod_{i=1}^t g_i^{b_i} \\
 & = & \theta\left(\underline{b_i}\right) \\
\end{array}$$
so that $\sigma = \theta$ as claimed.
