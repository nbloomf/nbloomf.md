---
title: From Arrows to Programs
author: nbloomf
---

Another nice consequence of wrapping up recursion in the $\natrec{\ast}{\ast}$ function is that it allows us to **write programs, independent of any implementation, and prove things about them**. We'll see some examples of this in a moment.

First we need to establish a structural result: every natural number is either $\zero$ or of the form $\next(n)$ for some $n$.

<div class="result">
<div class="lemma">
<p>If $n \in \mathbb{N}$, then either $n = \zero$ or $n = \next(m)$ for some $m$.</p>
</div>

<div class="proof">
Suppose to the contrary that there is an element $s \in \nats$, not equal to $\zero$, which is not of the form $\next(m)$ for some $m$. Note that $\bool$, with the distinguished element $\btrue$ and the constant function $\const(\btrue) : \bool \rightarrow \bool$, is an iterative set. Let $\Theta$ denote the unique iterative homomorphism $\natrec{\btrue}{\const(\btrue)} : \nats \rightarrow \bool$.

Now we define another mapping $\Psi : \nats \rightarrow \bool$ as follows: $$\Psi(x) = \left\{ \begin{array}{ll} \Theta(x) & \mathrm{if}\ x \neq s \\ \bnot(\Theta(x)) & \mathrm{if}\ x = s \end{array} \right.$$ We claim that $\Psi$ is an iterative homomorphism. To see this, note that $$\Psi(\zero) = \Theta(\zero) = \btrue$$ (since $\zero \neq s$) and that if $x \in \nats$, $$\Psi(\next(x)) = \Theta(\next(x)) = (\const\ \btrue)(\Theta(x)) = \btrue = (\const\ \btrue)(\Psi(x))$$ (since $\next(x) \neq s$). That is, $\Psi$ is an iterative homomorphism from $(\nats, \zero, \next)$ to $(\bool, \btrue, \const(\btrue))$, and since $\Theta$ is unique, we have $\Psi = \Theta$. But this implies that $\Theta(s) = \Psi(s) = \bnot(\Theta(s))$, which is absurd.
</div>
</div>
