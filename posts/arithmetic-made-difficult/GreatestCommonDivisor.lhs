---
title: Greatest Common Divisor
author: nbloomf
date: 2017-04-10
tags: arithmetic-made-difficult, literate-haskell
---

> module GreatestCommonDivisor
>   ( gcd, lcm, _test_gcd_lcm
>   ) where
>
> import Prelude hiding (div, rem, gcd, lcm)
>
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> 
> import Test.QuickCheck

Today we'll define the greatest common divisor of two natural numbers. The usual way to do this (in books I've seen) is to define what it means to say that $d$ is a greatest common divisor of $a$ and $b$, then show (possibly nonconstructively) that any two $a$ and $b$ have a greatest common divisor, and finally establish the Euclidean algorithm that actually computes GCDs. We will work backwards: first *defining* the GCD of two natural numbers using the punchline of the Euclidean algorithm and then proving that the output of this function acts like the GCD.

We'll do this using bailout recursion. This definition will be trickier to work with than the others we've seen so far because the "countdown timer" is just for show -- we expect it to actually reach zero only in one special case. For this reason reasoning about the recursive step is awkward.

<div class="result">
<div class="defn"><p>
Define maps $\varphi : \nats \times \nats \rightarrow \nats$ by $$\varphi(a,b) = b,$$ then $\beta : \nats \times (\nats \times \nats) \rightarrow \bool$ by $$\beta(k,(a,b)) = \nleq(b,\next(\zero)),$$ then $\psi : \nats \times (\nats \times \nats) \rightarrow \nats$ by $$\psi(k,(a,b)) = \left\{\begin{array}{ll} a & \mathrm{if}\ b = \zero \\ \next(\zero) & \mathrm{otherwise}, \end{array}\right.$$ and $\omega : \nats \times (\nats \times \nats) \rightarrow \nats \times \nats$ by $$\omega(k,(a,b)) = (b, \nrem(a,b)).$$ We then define a map $\ngcd : \nats \times \nats \rightarrow \nats$ by $$\ngcd(a,b) = \bailrec{\varphi}{\beta}{\psi}{\omega}(\nplus(a,b))(a,b).$$
</p></div>
</div>

For brevity's sake, we let $\Theta = \bailrec{\varphi}{\beta}{\psi}{\omega}$ for the rest of this post. Now for a special case.

<div class="result">
<div class="lemma">
For all $a \in \nats$ we have the following.

1. $\ngcd(a,\zero) = a$.
2. $\ngcd(\zero,a) = a$.
3. $\ngcd(a,\next(\zero)) = \next(\zero)$.
4. $\ngcd(\next(\zero),a) = \next(\zero)$.
</div>

<div class="proof"><p>
1. If $a = \zero$, note that
$$\begin{eqnarray*}
 &   & \ngcd(\zero,\zero) \\
 & = & \Theta(\zero,(\zero,\zero)) \\
 & = & \varphi(\zero,\zero) \\
 & = & \zero \\
 & = & a
\end{eqnarray*}$$
as needed. If $a = \next(d)$, we have
$$\begin{eqnarray*}
 &   & \ngcd(a,\zero) \\
 & = & \Theta(\next(d),(a,\zero)) \\
 & = & \psi(d,(a,\zero)) \\
 & = & a
\end{eqnarray*}$$
as needed.
2. We consider three cases: $a = \zero$, $a = \next(\zero)$, and $a = \next(\next(m))$. If $a = \zero$ we have $$\ngcd(\zero,a) = \ngcd(\zero,\zero) = \zero = a$$ as claimed. If $a = \next(\zero)$ we have
$$\begin{eqnarray*}
 &   & \ngcd(\zero,a) \\
 & = & \Theta(\nplus(\zero,a),(\zero,a)) \\
 & = & \Theta(\next(\zero),(\zero,a)) \\
 & = & \psi(\zero,(\zero,a)) \\
 & = & \next(\zero) \\
 & = & a
\end{eqnarray*}$$
as claimed. Finally, if $a = \next(\next(m))$ we have
$$\begin{eqnarray*}
 &   & \ngcd(\zero,a) \\
 & = & \Theta(\nplus(\zero,a),(\zero,a)) \\
 & = & \Theta(\next(\next(m)),(\zero,a)) \\
 & = & \Theta(\next(m),\omega(\zero,a)) \\
 & = & \Theta(\next(m),(a,\zero)) \\
 & = & \psi(m,(a,\zero)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \ngcd(a,\next(\zero)) \\
 & = & \Theta(\next(a),(a,\next(\zero)) \\
 & = & \psi(a,(a,\next(\zero))) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed.
4. We consider three cases. If $a = \zero$, then $\ngcd(a,\next(\zero)) = \next(\zero) by (2). If $a = \next(\zero)$, then we have
$$\begin{eqnarray*}
 &   & \ngcd(\next(\zero),a) \\
 & = & \Theta(\next(\next(\zero)),(\next(\zero),a) \\
 & = & \psi(\next(\zero),(\next(\zero),a)) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed. And if $a = \next(\next(b))$, then we have
$$\begin{eqnarray*}
 &   & \ngcd(\next(\zero),a) \\
 & = & \Theta(\next(\next(b)),(\next(\zero),a) \\
 & = & \Theta(\next(b),(a,\next(\zero))) \\
 & = & \psi(b,(a,\next(\zero))) \\
 & = & \next(\zero)
\end{eqnarray*}$$
</p></div>
</div>

Next, we need a couple of technical lemmas. First one about remainders:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ with $\nleq(b,a)$, and suppose $b = \next(m)$. Then we have $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,m)).$$
</div>

<div class="proof"><p>
Say $a = \nplus(b,k)$. There are two possibilities for $k$; either $k = \zero$ or $k = \next(u)$ for some $u$. Suppose first that $k = \zero$. In this case we have $\nrem(a,b) = \zero$, so that $b = \nplus(b,\nrem(a,b))$ and $\nplus(b,m) = \nplus(a,b)$. Thus $$\nleq(b,\nplus(a,m))$$ as claimed.

Suppose instead that $k = \next(u)$. By the division algorithm, we have $b = \nplus(\nrem(a,b),h)$ for some $h$. Now
$$\begin{eqnarray*}
 &   & \nplus(a,m) \\
 & = & \nplus(\nplus(b,k),m) \\
 & = & \nplus(\nplus(b,\next(u)),m) \\
 & = & \nplus(\nplus(b,u),\next(m)) \\
 & = & \nplus(\nplus(b,u),b) \\
 & = & \nplus(\nplus(b,u),\nplus(\nrem(a,b),h)) \\
 & = & \nplus(\nplus(b,\nrem(a,b)),\nplus(u,h)).
\end{eqnarray*}$$
In particular, we have $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,m))$$ as claimed.
</p></div>
</div>

Now a technical lemma about the guts of $\ngcd$:

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ with $\nleq(b,a)$. Then for all $c \in \nats$, we have $$\Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\nplus(a,b),(a,b)).$$
</div>

<div class="proof"><p>
Let $A = \{(a,b) \in \nats \times \nats \mid \nleq(b,a)\}$, and define $B \subseteq A$ by $$B = \{(a,b) \in A \mid \forall c \in \nats, \Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\nplus(a,b),(a,b))\}.$$ Now define $f : A \rightarrow \nats$ by $f(a,b) = b$. We will show that $B = A$ by strong induction on $f$.

For the base case, suppose we have $(a,b) \in A$ such that $\zero = f(a,b) = b$. Note first that $$\Theta(\nplus(a,b),(a,b)) = \ngcd(a,b) = a.$$ Now there are two possibilities for $\nplus(\nplus(a,b),c)$. If $\nplus(\nplus(a,b),c) = \zero$, then we have $a = c = \zero$. In this case we have $$\Theta(\nplus(\nplus(a,b),c),(a,b)) = \Theta(\zero,(a,b)) = b = \zero = a$$ as claimed. If instead we have $\nplus(\nplus(a,b),c) = \next(d)$ for some $d$, then we have
$$\begin{eqnarray*}
 &   & \Theta(\nplus(\nplus(a,b),c),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & a
\end{eqnarray*}$$
(since $b = \zero$) as claimed. In either case, we have $(a,b) \in B$.

Now for the inductive step, suppose we have $n \in \nats$ such that $k \in B$ whenever $\nleq(k,n)$. Suppose now that $(a,b) \in A$ such that $b = f(a,b) = \next(n)$. We consider two cases: either $n = \zero$ or $n = \next(m)$ for some $m$.

Suppose $n = \zero$; then $b = \next(\zero)$. In this case we have $\nplus(a,b) = \next(d)$ for some $d$ and $\nplus(\nplus(a,b),c) = \next(e)$ for some $e$. Now
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & \next(\zero) \\
 & = & \psi(e,(a,b)) \\
 & = & \Theta(\next(e),(a,b)) \\
 & = & \Theta(\nplus(\nplus(a,b),c),(a,b))
\end{eqnarray*}$$
as claimed.

Suppose instead that $n = \next(m)$. By the previous lemma, note that $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,n)),$$ and thus we have $$\nplus(a,n) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Note also that $\nleq(\nrem(a,b),n)$ by the division algorithm; in particular, we have $(b,\nrem(a,b)) \in B$ by the induction hypothesis. Now we have
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(\nplus(a,n)),(a,b)) \\
 & = & \Theta(\nplus(a,n),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),u),(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),\nplus(u,c)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,n),c),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,b),c),(a,b))
\end{eqnarray*}$$
as claimed. Thus $(a,b) \in B$, and by strong induction we have $B = A$.
</p></div>
</div>

And a corollary:

<div class="result">
<div class="corollary">
Let $a,b \in \nats$ such that $\nleq(b,a)$. Then $$\ngcd(a,b) = \ngcd(b,\nrem(a,b)).$$
</div>

<div class="proof"><p>
We consider three possibilities for $b$: either $b = \zero$, $b = \next(\zero)$, or $b = \next(\next(m))$ for some $m$.

If $b = \zero$, then we have $\nrem(a,b) = a$. In this case $$\ngcd(a,b) = \ngcd(b,a) = \ngcd(b,\nrem(a,b))$$ as claimed.

If $b = \next(\zero)$, then we have $\nrem(a,b) = \zero$ and $\nplus(a,b) = \next(d)$ for some $d$. Now
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(d),(a,b)) \\
 & = & \psi(d,(a,b)) \\
 & = & \next(\zero) \\
 & = & b \\
 & = & \ngcd(b,\zero) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.

Finally, suppose $b = \next(\next(m))$. Again we have $$\nplus(a,\next(m)) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Now
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(\nplus(a,\next(m))),(a,b)) \\
 & = & \Theta(\nplus(a,\next(m)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),u),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b))) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

One more technical lemma.

<div class="result">
<div class="lemma">
Let $a,b,m \in \nats$ such that $\nleq(b,a)$, $a \neq b$, and $\nplus(a,b) = \next(\next(m))$. Then we have $$\Theta(\next(m),(a,b)) = \Theta(\next(\next(m)),(a,b)).$$
</div>

<div class="proof"><p>
We proceed by strong induction on $b$. For the base case $b = \zero$, note that
$$\begin{eqnarray*}
 &   & \Theta(\next(m),(a,b)) \\
 & = & \psi(m,(a,b)) \\
 & = & a \\
 & = & \psi(\next(m),(a,b)) \\
 & = & \Theta(\next(\next(m)),(a,b))
\end{eqnarray*}$$
as claimed.

For the inductive step, suppose we have $n \in \nats$ such that the implication holds whenever $\nleq(b,n)$, and suppose further that $b = \next(n)$ and $a \in \nats$ such that $\nleq(b,a)$, $a \neq b$, and $\nplus(a,b) = \next(\next(m))$. We have two possibilities for $n$: either $n = \zero$ or $n = \next(t)$. If $n = \zero$, we have $b = \next(\zero)$. In this case, note that
$$\begin{eqnarray*}
 &   & \Theta(\next(m),(a,b)) \\
 & = & \psi(m,(a,b)) \\
 & = & \next(\zero) \\
 & = & \psi(\next(m),(a,b)) \\
 & = & \Theta(\next(\next(m)),(a,b))
\end{eqnarray*}$$
as claimed. Suppose then that $n = \next(t)$, so that $b = \next(\next(t))$.

Note that $$a = \nplus(b,\next(k))$$ for some $k$, since $\nleq(a,b)$ with $a \neq b$. We also have $$b = \nplus(\nrem(a,b),\next(t))$$ for some $t$, since $\nleq(\nrem(a,b),b)$ and $\nrem(a,b) \neq b$. Now
$$\begin{eqnarray*}
 &   & \next(\next(m)) \\
 & = & \nplus(a,b) \\
 & = & \nplus(\nplus(b,\next(k)),\nplus(\nrem(a,b),\next(t))) \\
 & = & \next(\next(\nplus(\nplus(b,k),\nplus(\nrem(a,b),t)))) \\
 & = & \next(\next(\nplus(\nplus(b,\nrem(a,b)),\nplus(k,t)))) \\
\end{eqnarray*}$$
and thus $$m = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$ (we have $u = \nplus(k,t)$, but this is not important). Using the last technical lemma, we then have
$$\begin{eqnarray*}
 &   & \Theta(\next(m),(a,b)) \\
 & = & \psi(m,(a,b)) \\
 & = & \Theta(m,(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b))) \\
 & = & \Theta(\next(m),(b,\nrem(a,b))) \\
 & = & \psi(\next(m),(a,b) \\
 & = & \Theta(\next(\next(m)),(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now we are prepared to show that $\ngcd$ is commutative.

<div class="result">
<div class="corollary">
Let $a,b \in \nats$. Then $\ngcd(a,b) = \ngcd(b,a)$.
</div>

<div class="proof"><p>
We consider three possibilities for $\nplus(a,b)$: either $\nplus(a,b) = \zero$, or $\nplus(a,b) = \next(\zero)$, or $\nplus(a,b) = \next(\next(m))$ for some $m$.

If $\nplus(a,b) = \zero$ then $a = b = \zero$. In this case we have $$\ngcd(a,b) = \zero = \ngcd(b,a)$$ as needed.

Suppose $\nplus(a,b) = \next(\zero)$. Now there are two possibilities. If $a = \zero$, we have $$\ngcd(a,b) = b = \ngcd(b,a),$$ and similarly if $b = \zero$.

Suppose $\nplus(a,b) = \next(\next(\zero))$. Now there are three possibilites. If $a = \zero$, we have $$\ngcd(a,b) = b = \ngcd(b,a);$$ likewise if $b = \zero$. Suppose then that $a = b = \next(\zero)$. Then we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\next(\next(\zero)),(a,b)) \\
 & = & \psi(\next(\zero),(a,b)) \\
 & = & \next(\zero),
\end{eqnarray*}$$
and similarly, $\ngcd(b,a) = \next(\zero)$ as needed.

Suppose then that $\nplus(a,b) = \next(\next(\next(m)))$ for some $m$. If $a = b$, we have $\ngcd(a,b) = \ngcd(b,a)$ as claimed. Suppose then that $a \neq b$; without loss of generality, suppose that $\nleq(a,b)$ is false. Then $\nleq(b,a)$ is true. In particular we must have $a = \next(\next(t))$ for some $t$, since otherwise $\nleq(a,b)$. Note then that (using the lemma) we have
$$\begin{eqnarray*}
 &   & \ngcd(b,a) \\
 & = & \Theta(\next(\next(\next(m))),(b,a)) \\
 & = & \Theta(\next(\next(m)),(a,b)) \\
 & = & \Theta(\next(\next(\next(m))),(a,b)) \\
 & = & \ngcd(a,b)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$.
</div>

<div class="proof"><p>
We've already established this in the case $\nleq(b,a) = \btrue$; so suppose instead that $\nleq(b,a) = \bfalse$. In this case we have $\nrem(a,b) = a$, so that
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \ngcd(b,a) \\
 & = & \ngcd(b,\nrem(a,b)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Working with the definition of $\ngcd$ is tedious! As quickly as possible we'd like to characterize it in terms of some kind of "universal property" -- that's precisely what we'll do next.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\ndiv(\ngcd(a,b),a)$ and $\ndiv(\ngcd(a,b),b)$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$.
</div>

<div class="proof"><p>
1. Let $$A = \{ (a,b) \in \nats \times \nats \mid \ndiv(\ngcd(a,b),a)\ \mathrm{and}\ \ndiv(\ngcd(a,b),b) \}$$ and define $f : \nats \times \rightarrow \nats$ by $f(a,b) = b$. We will show that $A = \nats \times \nats$ by strong induction on $f$. For the base case, suppose we have $\zero = f(a,b) = b$. Then $\ngcd(a,b) = a$, and so $\ndiv(\ngcd(a,b),a)$ and of course $\ndiv(\ngcd(a,b),b)$ as claimed. For the inductive step, suppose we have $n \in \nats$ such that the conclusion holds whenever $\nleq(f(a,b),n)$, and suppose $b = f(a,b) = \next(n)$. Now $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$. We also have $\nleq(\nrem(a,b),n) = \btrue$, so by the inductive hypothesis, $$\ndiv(\ngcd(a,b),b)\ \mathrm{and}\ \ndiv(\ngcd(a,b),\nrem(a,b)).$$ Say $$b = \ntimes(\ngcd(a,b),u)$$ and $$\nrem(a,b) = \ntimes(\ngcd(a,b),v).$$ Now we have
$$\begin{eqnarray*}
 &   & a \\
 & = & \nplus(\ntimes(\nquo(a,b),b),\nrem(a,b)) \\
 & = & \nplus(\ntimes(\nquo(a,b),\ntimes(\ngcd(a,b),u)),\ntimes(\ngcd(a,b),v)) \\
 & = & \ntimes(\ngcd(a,b),\nplus(\ntimes(\nquo(a,b),u),v))
\end{eqnarray*}$$
so $\ndiv(\ngcd(a,b),a)$, and thus $(a,b) \in A$. By strong induction, $A = \nats \times \nats$ as needed.
2. Let $$A = \{ (a,b) \in \nats \times \nats \mid \forall c \in \nats. \mathrm{if}\ \ndiv(c,a)\ \mathrm{and}\ \ndiv(c,b)\ \mathrm{then}\ \ndiv(c,\ngcd(a,b)) \}$$ and define $f : \nats \times \nats \rightarrow \nats$ by $f(a,b) = b$. We show that $A = \nats \times \nats$ by strong induction on $f$. For the base case, suppose $\zero = f(a,b) = b$. Now we have $\ngcd(a,b) = a$. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$. For the inductive step, suppose we have $n \in \nats$ such that the implication holds for all $c$ when $\nleq(f(a,b),n)$, and say $b = f(a,b) = \next(n)$. We consider two cases. If $\nleq(b,a)$ is false, then by the induction hypothesis the implication holds. Suppose then that $\nleq(b,a)$ is true. Now $$\ngcd(a,b) = \ngcd(b,\nrem(a,b))$$ and $\nleq(\nrem(a,b),n)$. By the induction hypothesis, the implication holds for $\nrem(a,b)$. Suppose then that $\ndiv(c,a)$ and $\ndiv(c,b)$; we have $\ndiv(c,\nrem(a,b))$, so that $\ndiv(c,\ngcd(b,\nrem(a,b)))$, and thus $\ndiv(c,\ngcd(a,b))$ as needed.
</p></div>
</div>

From here, more properties of $\ngcd$ are much easier to prove.

<div class="result">
<div class="corollary">
Let $a,b,c \in \nats$. Then we have the following.

1. $\ngcd(a,a) = a$.
2. $\ngcd(\ngcd(a,b),c) = \ngcd(a,\ngcd(b,c))$.
</div>

<div class="proof"><p>
1. Note that $\ndiv(a,a)$, so that $\ndiv(a,\ngcd(a,a))$. But we also have $\ndiv(\ngcd(a,a),a)$. By the antisymmetry of $\ndiv$, $a = \ngcd(a,a)$.
2. (@@@)
</p></div>
</div>

We now define the "opposite" concept, least common multiple, in terms of $\ngcd$.

<div class="result">
<div class="defn"><p>
Define $\nlcm : \nats \times \nats \rightarrow \nats$ by $$\nlcm(a,b) = \nquo(\ntimes(a,b),\ngcd(a,b)).$$
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``gcd`` and ``lcm``:

> gcd :: (Natural t) => t -> t -> t
> gcd a b = (bailoutRec phi beta psi omega) (plus a b) (a,b)
>   where
>     phi (_,b) = b
>     beta _ (_,b) = leq b (next zero)
>     omega _ (a,b) = (b, rem a b)
> 
>     psi _ (a,b) = if b == zero
>       then a
>       else next zero
> 
> 
> lcm :: (Natural t) => t -> t -> t
> lcm a b = quo (times a b) (gcd a b)

Property tests for ``gcd``:

> -- gcd(a,0) == a and gcd(0,a) == a
> _test_gcd_zero :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_zero _ a b = and
>   [ a == gcd a zero
>   , a == gcd zero a
>   ]
> 
> 
> -- gcd(a,b) == gcd(b,rem(a,b))
> _test_gcd_rem :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_rem _ a b =
>   (gcd a b) == (gcd b (rem a b))
> 
> 
> -- gcd(a,b) == gcd(b,a)
> _test_gcd_commutative :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_commutative _ a b =
>   (gcd a b) == (gcd b a)
> 
> 
> -- div(gcd(a,b),a) and div(gcd(a,b),b)
> _test_gcd_div_args :: (Natural t) => t -> t -> t -> Bool
> _test_gcd_div_args _ a b = and
>   [ div (gcd a b) a
>   , div (gcd a b) b
>   ]
> 
> 
> -- gcd(a,a) = a
> _test_gcd_idempotent :: (Natural t) => t -> t -> Bool
> _test_gcd_idempotent _ a =
>   (gcd a a) == a
> 
> 
> -- gcd(gcd(a,b),c) == gcd(a,gcd(b,c))
> _test_gcd_associative :: (Natural t) => t -> t -> t -> t -> Bool
> _test_gcd_associative _ a b c =
>   (gcd (gcd a b) c) == (gcd a (gcd b c))

Property tests for ``lcm``:

> -- div(a,lcm(a,b)) and div(b,lcm(a,b))
> _test_lcm_div_args :: (Natural t) => t -> t -> t -> Bool
> _test_lcm_div_args _ a b = and
>   [ div a (lcm a b)
>   , div b (lcm a b)
>   ]
> 
> 
> -- lcm(a,a) = a
> _test_lcm_idempotent :: (Natural t) => t -> t -> Bool
> _test_lcm_idempotent _ a =
>   (lcm a a) == a

And the suite:

> -- run all tests for div
> _test_gcd_lcm :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_gcd_lcm t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_gcd_zero t)
>   , quickCheckWith args (_test_gcd_rem t)
>   , quickCheckWith args (_test_gcd_commutative t)
>   , quickCheckWith args (_test_gcd_div_args t)
>   , quickCheckWith args (_test_gcd_idempotent t)
>   , quickCheckWith args (_test_gcd_associative t)
> 
>   , quickCheckWith args (_test_lcm_div_args t)
>   , quickCheckWith args (_test_lcm_idempotent t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
