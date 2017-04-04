---
title: Really Simple Equations
author: nbloomf
date: 2017-04-01
tags: arithmetic-made-difficult
---

In this post we will take a break and solve some equations in the natural numbers. These equations will be *really* simple, but we have to start somewhere! In the more familiar notation we will solve the following equations: $$\begin{array}{rrr} a+b=0 & \quad a+b=1 & \quad a+b=2 \\ ab=0 & \quad ab=1 & \quad ab=2 \end{array}$$

Our strategy is based on two of the Peano axioms. Specifically, (1) $\zero = \next(m)$ has no solution $m \in \nats$, and (2) every element of $\nats$ is either $\zero$ or of the form $\next(m)$ for some $m \in \nats$. Property (2) can be used to perform case analysis on $\nats$, like so:

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\nplus(a,b) = \zero$, then $a = b = \zero$.
</div>

<div class="proof"><p>
Suppose $\nplus(a,b) = \zero$. Note that either $a = \zero$ or $a = \next(m)$ for some $m \in \nats$. If $a = \next(m)$, then $$\zero = \nplus(a,b) = \nplus(\next(m),b) = \next(\nplus(m,b)),$$ a contradiction. So we have $a = \zero$. But now $\zero = \nplus(\zero,b) = b$ as claimed.
</p></div>
</div>

The following generalization will be handy.

<div class="result">
<div class="thm">
We have the following.

1. Every natural number is either $\zero$, $\next(\zero)$, or of the form $\next(\next(m))$ for some $m \in \nats$.
2. Every natural number is either $\zero$, $\next(\zero)$, $\next(\next(\zero))$, or of the form $\next(\next(\next(m)))$ for some $m \in \nats$.
</div>

<div class="proof"><p>
1. Let $n \in \nats$. Either $n = \zero$ or $n = \next(k)$ for some $k \in \nats$; but now either $k = \zero$ or $k = \next(m)$ for some $m \in \nats$. So either $n = \zero$, $n = \next(\zero)$, of $n = \next(\next(m))$ for some $m \in \nats$.
2. Similar to (1).
</p></div>
</div>

This will allow us to use more detailed case analysis on $\nats$.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\nplus(a,b) = \next(\zero)$, then $(a,b)$ is either $(\zero,\next(\zero))$ or $(\next(\zero),\zero)$.
</div>

<div class="proof"><p>
Note that either $a = \zero$, $a = \next(\zero)$, or $a = \next(\next(m))$ for some $m \in \nats$.

* If $a = \next(\next(m))$ for some $m \in \nats$, we have $$\begin{eqnarray*} & & \next(\zero) \\ & = & \nplus(a,b) \\ & = & \nplus(\next(\next(m)),b) \\ & = & \next(\next(\nplus(m,b))), \end{eqnarray*}$$ so that $\zero = \next(\nplus(m,b))$, a contradiction.
* If $a = \next(\zero)$, then we have $\nplus(\next(\zero),\zero) = \next(\zero) = \nplus(\next(\zero),b)$, so that $b = \zero$ as claimed.
* If $a = \zero$, then $\next(\zero) = \nplus(\zero,b) = b$ as claimed.
</p></div>
</div>

Ain't this fun!

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\nplus(a,b) = \next(\next(\zero))$, then $(a,b)$ is either $(\zero,\next(\next(\zero)))$ or $(\next(\zero),\next(\zero))$ or $(\next(\next(\zero)),\zero)$.
</div>

<div class="proof"><p>
Note that either $a = \zero$, $a = \next(\zero)$, $a = \next(\next(\zero))$, or $a = \next(\next(\next(m)))$ for some $m \in \nats$.

* If $a = \next(\next(\next(m)))$ for some $m \in \nats$, we have $$\begin{eqnarray*} & & \next(\next(\zero)) \\ & = & \nplus(a,b) \\ & = & \nplus(\next(\next(\next(m))),b) \\ & = & \next(\next(\next(\nplus(m,b)))), \end{eqnarray*}$$ so that $\zero = \next(\nplus(m,b))$, a contradiction.
* If $a = \next(\next(\zero))$, then we have $$\begin{eqnarray*} & & \nplus(\next(\next(\zero)),\zero) \\ & = & \next(\next(\zero)) \\ & = & \nplus(\next(\next(\zero)),b) \end{eqnarray*}$$ so that $b = \zero$ as claimed.
* If $a = \next(\zero)$, then we have $$\next(\next(\zero)) = \nplus(\next(\zero),b) = \next(\nplus(\zero,b)) = \next(b)$$ so that $b = \next(\zero)$ as claimed.
* If $a = \zero$, then $\next(\next(\zero)) = \nplus(\zero,b) = b$ as claimed.
</p></div>
</div>

Okay this is boring. How about some equations with $\ntimes$?

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\ntimes(a,b) = \zero$, then either $a = \zero$ or $b = \zero$.
</div>

<div class="proof"><p>
Suppose that neither $a$ nor $b$ is $\zero$; then we have $a = \next(h)$ and $b = \next(k)$ for some $h,k \in \nats$. Now $$\begin{eqnarray*} & & \zero \\ & = & \ntimes(a,b) \\ & = & \ntimes(\next(h),\next(k)) \\ & = & \nplus(\ntimes(h,\next(k)),\next(k)) \\ & = & \next(\nplus(\ntimes(h,\next(k)),k)), \end{eqnarray*}$$ a contradiction. So we must have either $a = \zero$ or $b = \zero$. Note also that in either case we indeed have $\ntimes(a,b) = \zero$.
</p></div>
</div>

woo

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\ntimes(a,b) = \next(\zero)$, then $(a,b)$ is $(\next(\zero),\next(\zero))$.
</div>

<div class="proof"><p>
Suppose we have $\ntimes(a,b) = \next(\zero)$. Note that either $a = \zero$ or $a = \next(\zero)$ or $a = \next(\next(m))$ for some $m \in \nats$.

* If $a = \zero$ we have $\next(\zero) = \ntimes(a,b) = \zero$, a contradiction.
* If $a = \next(\zero)$, we have $$\next(\zero) = \ntimes(\next(\zero),b) = b$$ as claimed.
* If $a = \next(\next(m))$ for some $m \in \nats$, we have $$\begin{eqnarray*} \next(\zero) & = & \ntimes(a,b) \\ & = & \ntimes(\next(\next(m)),b) \\ & = & \nplus(b,\ntimes(\next(m),b)). \end{eqnarray*}$$ There are now two possibilties for $b$. If $b = \zero$, we have $\zero = \next(\zero)$, a contradiction. If $b = \next(k)$ with $k \in \nats$, we have $$\next(\zero) = \nplus(\next(k),\ntimes(\next(m),\next(k)))$$ so that $$\zero = \nplus(k,\ntimes(\next(m),\next(k))).$$ But now we have $k = \zero$ and $$\zero = \ntimes(\next(m),\next(\zero)) = \next(m),$$ a contradiction.
</p></div>
</div>

One more:

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\ntimes(a,b) = \next(\next(\zero))$, then $(a,b)$ is either $(\next(\next(\zero)),\next(\zero))$ or $(\next(\zero),\next(\next(\zero)))$.
</div>

<div class="proof"><p>
Suppose we have $\ntimes(a,b) = \next(\next(\zero))$. Note that either $a = \zero$ or $a = \next(\zero)$ or $a = \next(\next(\zero))$ or $a = \next(\next(\next(m)))$ for some $m \in \nats$.

* If $a = \zero$ we have $\next(\zero) = \ntimes(a,b) = \zero$, a contradiction.
* If $a = \next(\zero)$, we have $$\next(\next(\zero)) = \ntimes(\next(\zero),b) = b$$ as claimed.
* If $a = \next(\next(\zero))$, we have $$\ntimes(\next(\next(\zero)),\next(\zero)) = \next(\next(\zero)) = \ntimes(\next(\next(\zero)),b)$$ so that $b = \next(\zero)$ as claimed.
* Suppose we have $a = \next(\next(\next(m)))$ for some $m \in \nats$. Now $$\begin{eqnarray*} & & \next(\next(\zero)) \\ & = & \ntimes(\next(\next(\next(m))),b) \\ & = & \nplus(\ntimes(\next(\next(m)),b),b). \end{eqnarray*}$$ If $b = \zero$, then we have $\next(\next(\zero)) = \zero$, a contradiction. Thus $b = \next(k)$ for some $k \in \nats$. This leaves two possibilities: $$(\ntimes(\next(\next(m)),\next(k)),\next(k))$$ is either $(\next(\zero),\next(\zero))$ or $(\zero,\next(\next(\zero)))$. If $b = \next(\zero)$, we have $\next(\next(\zero)) = \next(\next(\next(m)))$ for some $m$, a contradiction. If $b = \next(\next(\zero))$ and $\ntimes(\next(\next(m)),b) = \zero$, we have either $b = \zero$ (a contradiction) or $\next(\next(m)) = \zero$ (also a contradiction).
</p></div>
</div>

This is kind of ridiculous! But we're doing number theory from first principles, so ridiculousness is kind of the point.
