---
title: Greatest Common Divisor
author: nbloomf
date: 2017-04-10
tags: arithmetic-made-difficult, literate-haskell
---

> module GreatestCommonDivisor
>   ( gcd, _test_gcd, main_gcd
>   ) where
>
> import Booleans
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo
> import DivisionAlgorithm
> import Divides
> 
> import Prelude (Show, Int, IO, sequence_)
> import Test.QuickCheck

Today we'll define the greatest common divisor of two natural numbers. The usual way to do this (in books I've seen) is to define what it means to say that $d$ is a greatest common divisor of $a$ and $b$, then show (possibly nonconstructively) that any two $a$ and $b$ have a greatest common divisor, and finally establish the Euclidean algorithm that actually computes GCDs. We will work backwards: first *defining* the GCD of two natural numbers using the punchline of the Euclidean algorithm and then proving that the output of this function acts like the GCD.

We'll do this using bailout recursion. This definition will be trickier to work with than the others we've seen so far because the "countdown timer" is just for show -- we don't expect it to actually reach zero. For this reason reasoning about the recursive step is awkward.

<div class="result">
<div class="defn"><p>
Define maps $\varphi : \nats \times \nats \rightarrow \nats$ by $$\varphi(a,b) = b,$$ then $\beta : \nats \times (\nats \times \nats) \rightarrow \bool$ by $$\beta(k,(a,b)) = \iszero(b),$$ then $\psi : \nats \times (\nats \times \nats) \rightarrow \nats$ by $$\psi(k,(a,b)) = a,$$ and $\omega : \nats \times (\nats \times \nats) \rightarrow \nats \times \nats$ by $$\omega(k,(a,b)) = (b, \nrem(a,b)).$$ We then define a map $\ngcd : \nats \times \nats \rightarrow \nats$ by $$\ngcd(a,b) = \bailrec{\varphi}{\beta}{\psi}{\omega}(\next(\nplus(a,b)))(a,b).$$
</p></div>
</div>

For brevity's sake, we let $\Theta = \bailrec{\varphi}{\beta}{\psi}{\omega}$ for the rest of this post.

Because of the way $\ngcd$ uses its countdown parameter, we will need a couple of technical lemmas about $\Theta$. The first gives a bound on the parts of a long division problem.

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

The next lemma says that we can add a constant $c$ to the initial countdown timer of $\Theta$ without affecting the final value.

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ with $\nleq(b,a)$. Then for all $c \in \nats$, we have $$\Theta(\nplus(\next(\nplus(a,b)),c),(a,b)) = \Theta(\next(\nplus(a,b)),(a,b)).$$
</div>

<div class="proof"><p>
Let $A = \{(a,b) \in \nats \times \nats \mid \nleq(b,a)\}$. For brevity, we define functions $M : \nats \times \nats \times \nats \rightarrow \nats$ and $N : \nats \times \nats \rightarrow \nats$ by
$$\begin{eqnarray*}
M(a,b,c) & = & \Theta(\nplus(\next(\nplus(a,b)),c),(a,b)) \\
N(a,b)   & = & \Theta(\next(\nplus(a,b)),(a,b)),
\end{eqnarray*}$$
and finally define $B \subseteq A$ by $$B = \{(a,b) \in A \mid \forall c \in \nats, M(a,b,c) = N(a,b) \}.$$ Now define $f : A \rightarrow \nats$ by $f(a,b) = b$. We will show that $B = A$ by strong induction on $f$.

For the base case, suppose we have $(a,b) \in A$ such that $\zero = f(a,b) = b$. Now for all $c \in \nats$, we have
$$\begin{eqnarray*}
 &   & N(a,\zero) \\
 & = & \Theta(\next(\nplus(a,\zero)),(a,\zero)) \\
 & = & \psi(\nplus(a,\zero),(a,\zero)) \\
 & = & a \\
 & = & \psi(\nplus(\nplus(a,\zero),c),(a,\zero)) \\
 & = & \Theta(\next(\nplus(\nplus(a,\zero),c)),(a,\zero)) \\
 & = & \Theta(\nplus(\next(\nplus(a,\zero)),c),(a,\zero)) \\
 & = & M(a,\zero,c).
\end{eqnarray*}$$
Thus we have $(a,b) \in B$.

Now for the inductive step, suppose we have $n \in \nats$ such that $(a,b) \in B$ whenever $b = f(a,b) = k$ and $\nleq(k,n)$. Suppose further that $(a,b) \in A$ such that $b = f(a,b) = \next(n)$.

By the previous lemma, note that $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,n)),$$ and thus we have $$\nplus(a,n) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Note also that $\nleq(\nrem(a,b),n)$ by the division algorithm; in particular, we have $(b,\nrem(a,b)) \in B$ by the induction hypothesis. Now we have
$$\begin{eqnarray*}
 &   & N(a,b) \\
 & = & \Theta(\next(\nplus(a,b)),(a,b)) \\
 & = & \Theta(\nplus(a,b),(b,\nrem(a,b))) \\
 & = & \Theta(\next(\nplus(a,n)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\next(\nplus(b,\nrem(a,b))),u),(b,\nrem(a,b)) \\
 & = & M(b,\nrem(a,b),u) \\
 & = & N(b,\nrem(a,b)) \\
 & = & M(b,\nrem(a,b),\nplus(u,c)) \\
 & = & \Theta(\nplus(\next(\nplus(b,\nrem(a,b))),\nplus(u,c)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,n),c),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(a,b),c),(a,b)) \\
 & = & M(a,b,c)
\end{eqnarray*}$$
as claimed. Thus $(a,b) \in B$, and by strong induction we have $B = A$.
</p></div>
</div>

The next lemma says that we can subtract 1 from the initial countdown timer of $\Theta$ without affecting the final value.

<div class="result">
<div class="lemma">
Let $a,b \in \nats$ such that $\nleq(b,a)$ and $a \neq b$. Then we have $$\Theta(\next(\nplus(a,b)),(a,b)) = \Theta(\nplus(a,b)),(a,b)).$$
</div>

<div class="proof"><p>
Note that, since $a \neq b$, we must have $\nplus(a,b) = \next(m)$ for some $m \in \nats$.

We proceed by strong induction on $b$. For the base case $b = \zero$, note that
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,\zero),(a,\zero)) \\
 & = & \Theta(\next(m),(a,\zero)) \\
 & = & \psi(m,(a,\zero)) \\
 & = & a \\
 & = & \psi(\next(m),(a,\zero)) \\
 & = & \Theta(\next(\next(m)),(a,\zero)) \\
 & = & \Theta(\next(\nplus(a,\zero)),(a,\zero))
\end{eqnarray*}$$
as claimed.

For the inductive step, suppose we have $n \in \nats$ such that the implication holds whenever $\nleq(b,n)$, and suppose further that $b = \next(n)$ and $a \in \nats$ such that $\nleq(b,a)$ and $a \neq b$.

By the next-to-last lemma, note that $$\nleq(\nplus(b,\nrem(a,b)),\nplus(a,n)),$$ and thus we have $$\nplus(a,n) = \nplus(\nplus(b,\nrem(a,b)),u)$$ for some $u$. Note also that $\nleq(\nrem(a,b),n)$ by the division algorithm. Now, borrowing the $M$ and $N$ notation from the proof of the last lemma, we have
$$\begin{eqnarray*}
 &   & \Theta(\nplus(a,b),(a,b)) \\
 & = & \Theta(\next(\nplus(a,n)),(a,b)) \\
 & = & \Theta(\nplus(a,n),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),u),(b,\nrem(a,b))) \\
 & = & M(b,\nrem(a,b),u) \\
 & = & N(b,\nrem(a,b)) \\
 & = & M(b,\nrem(a,b),\next(u)) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),\next(u)),(b,\nrem(a,b))) \\
 & = & \Theta(\next(\nplus(\nplus(b,\nrem(a,b)),u)),(b,\nrem(a,b))) \\
 & = & \Theta(\next(\nplus(a,n)),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(a,b),(b,\nrem(a,b))) \\
 & = & \Theta(\next(\nplus(a,b)),(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The last two lemmas will enable us to reason about $\ngcd$ recursively. For example, we are prepared to show that $\ngcd$ is commutative.

<div class="result">
<div class="corollary">
Let $a,b \in \nats$. Then $\ngcd(a,b) = \ngcd(b,a)$.
</div>

<div class="proof"><p>
We consider two cases: either $a = b$ or $a \neq b$. Of course the result holds if $a = b$; suppose instead that $a \neq b$, and without loss of generality, say $\nleq(b,a)$ is false. Then we have $\nleq(a,b)$ and $a \neq b$. Now $b \neq \zero$ and $\nrem(b,a) = a$, and we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\next(\nplus(a,b))),(a,b)) \\
 & = & \Theta(\nplus(a,b),(b,a)) \\
 & = & \Theta(\nplus(b,a),(b,a)) \\
 & = & \Theta(\next(\nplus(b,a)),(b,a)) \\
 & = & \ngcd(b,a)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We can show that $\ngcd$ is idempotent:

<div class="result">
<div class="corollary">
Let $a \in \nats$. Then $$\ngcd(a,a) = a.$$
</div>

<div class="proof"><p>
We consider two cases: either $a = \zero$ or $a = \next(m)$ for some $m$. If $a = \zero$, then we have
$$\begin{eqnarray*}
 &   & \ngcd(\zero,\zero) \\
 & = & \Theta(\next(\nplus(\zero,\zero)),(\zero,\zero)) \\
 & = & \psi(\zero,(\zero,\zero)) \\
 & = & \zero
\end{eqnarray*}$$
as claimed. If $a = \next(m)$, then $\nrem(a,a) = \zero$, and we have
$$\begin{eqnarray*}
 &   & \ngcd(a,a) \\
 & = & \Theta(\next(\nplus(a,a)),(a,a)) \\
 & = & \Theta(\next(\nplus(m,a)),(a,\zero)) \\
 & = & \psi(\nplus(m,a),(a,\zero)) \\
 & = & a
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now for a special case.

<div class="result">
<div class="lemma">
For all $a \in \nats$ we have the following.

1. $\ngcd(a,\zero) = a$.
2. $\ngcd(a,\next(\zero)) = \next(\zero)$.
</div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \ngcd(a,\zero) \\
 & = & \Theta(\next(\zero),(a,\zero)) \\
 & = & \psi(\zero,(a,\zero)) \\
 & = & a
\end{eqnarray*}$$
as needed.
2. Note that
$$\begin{eqnarray*}
 &   & \ngcd(a,\next(\zero)) \\
 & = & \Theta(\next(\next(a)),(a,\next(\zero)) \\
 & = & \Theta(\next(a),(\next(\zero),\zero)) \\
 & = & \psi(a,(\next(\zero),\zero)) \\
 & = & \next(\zero)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We can now give an unqualified recursive characterization of $\ngcd$:

<div class="result">
<div class="corollary">
Let $a,b \in \nats$. Then $$\ngcd(a,b) = \ngcd(b,\nrem(a,b)).$$
</div>

<div class="proof"><p>
We consider two cases: $\nleq(b,a)$ is either false or true. If $\nleq(b,a)$ is false, then $\nleq(a,b)$ and $a \neq b$, and we have $\nrem(a,b) = a$. Then by commutativity we have $$\ngcd(a,b) = \ngcd(b,a) = \ngcd(b,\nrem(a,b))$$ as claimed.

Suppose instead that $\nleq(b,a)$. If $a = b$, then $\nrem(a,b) = \zero$, and we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \ngcd(b,b) \\
 & = & b \\
 & = & \ngcd(b,\zero) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.

Suppose then that $a \neq b$. In this case we have $b \neq \zero$, $\nleq(\nrem(a,b),b)$, $b \neq \nrem(a,b)$, and $\nleq(\nrem(a,b),a)$, so that $$a = \nplus(\nrem(a,b),k)$$ for some $k$. Now so that
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \Theta(\next(\nplus(a,b)),(a,b)) \\
 & = & \Theta(\nplus(a,b),(b,\nrem(a,b)) \\
 & = & \Theta(\nplus(\nplus(b,\nrem(a,b)),k),(b,\nrem(a,b))) \\
 & = & \Theta(\nplus(b,\nrem(a,b)),(b,\nrem(a,b))) \\
 & = & \Theta(\next(\nplus(b,\nrem(a,b))),(b,\nrem(a,b)) \\
 & = & \ngcd(b,\nrem(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Working with the definition of $\ngcd$ is tedious! The next theorem characterizes $\ngcd(a,b)$ in terms of a useful "universal property": it is a common divisor of $a$ and $b$, and among the common divisors of $a$ and $b$, it is the "largest" in an appropriate sense. We can use this property to avoid having to look inside the implementation of $\ngcd$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\ndiv(\ngcd(a,b),a)$ and $\ndiv(\ngcd(a,b),b)$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$.
</div>

<div class="proof"><p>
1. Let $$A = \{ (a,b) \in \nats \times \nats \mid \ndiv(\ngcd(a,b),a)\ \mathrm{and}\ \ndiv(\ngcd(a,b),b) \}$$ and define $f : \nats \times \nats \rightarrow \nats$ by $f(a,b) = b$. We will show that $A = \nats \times \nats$ by strong induction on $f$. For the base case, suppose we have $\zero = f(a,b) = b$. Then $\ngcd(a,b) = a$, and so $\ndiv(\ngcd(a,b),a)$ and of course $\ndiv(\ngcd(a,b),b)$ as claimed. For the inductive step, suppose we have $n \in \nats$ such that the conclusion holds whenever $\nleq(f(a,b),n)$, and suppose $b = f(a,b) = \next(n)$. Now $\ngcd(a,b) = \ngcd(b,\nrem(a,b))$. We also have $\nleq(\nrem(a,b),n) = \btrue$, so by the inductive hypothesis, $$\ndiv(\ngcd(a,b),b)\ \mathrm{and}\ \ndiv(\ngcd(a,b),\nrem(a,b)).$$ Say $$b = \ntimes(\ngcd(a,b),u)$$ and $$\nrem(a,b) = \ntimes(\ngcd(a,b),v).$$ Now we have
$$\begin{eqnarray*}
 &   & a \\
 & = & \nplus(\ntimes(\nquo(a,b),b),\nrem(a,b)) \\
 & = & \nplus(\ntimes(\nquo(a,b),\ntimes(\ngcd(a,b),u)),\ntimes(\ngcd(a,b),v)) \\
 & = & \ntimes(\ngcd(a,b),\nplus(\ntimes(\nquo(a,b),u),v))
\end{eqnarray*}$$
so $\ndiv(\ngcd(a,b),a)$, and thus $(a,b) \in A$. By strong induction, $A = \nats \times \nats$ as needed.
2. We proceed by strong induction on $b$. For the base case, suppose $b = \zero$. Now we have $\ngcd(a,b) = a$. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,\ngcd(a,b))$ as needed. For the inductive step, suppose we have $n \in \nats$ such that the implication holds for all $c$ when $\nleq(b,n)$, and say $b = \next(n)$. We consider two cases. If $\nleq(b,a)$ is false, we have $\ngcd(a,b) = \ngcd(b,a)$ and by the induction hypothesis the implication holds. Suppose then that $\nleq(b,a)$ is true. Now $$\ngcd(a,b) = \ngcd(b,\nrem(a,b))$$ and $\nleq(\nrem(a,b),n)$. By the induction hypothesis, the implication holds for $\nrem(a,b)$. Suppose then that $\ndiv(c,a)$ and $\ndiv(c,b)$; we have $\ndiv(c,\nrem(a,b))$, so that $\ndiv(c,\ngcd(b,\nrem(a,b)))$, and thus $\ndiv(c,\ngcd(a,b))$ as needed.
</p></div>
</div>

And $\ngcd(a,b)$ is unique with this property.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Suppose $m \in \nats$ satisfies the following.

1. $\ndiv(m,a)$ and $\ndiv(m,b)$.
2. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $\ndiv(c,m)$.

Then $m = \ngcd(a,b)$.
</div>

<div class="proof"><p>
Since $\ndiv(m,a)$ and $\ndiv(m,b)$, we have $\ndiv(m,\ngcd(a,b))$. But a similar argument shows that $\ndiv(\ngcd(a,b),m)$. By antisymmetry we have $m = \ngcd(a,b)$ as claimed.
</p></div>
</div>

From here, more properties of $\ngcd$ are much easier to prove.

<div class="result">
<div class="corollary">
Let $a,b,c \in \nats$. Then we have the following.

1. $\ngcd(\ngcd(a,b),c) = \ngcd(a,\ngcd(b,c))$.
2. $\ngcd(a,b) = a$ if and only if $\ndiv(a,b)$.
3. $\ngcd(\ntimes(a,c),\ntimes(b,c)) = \ntimes(\ngcd(a,b),c)$.
4. If $\ngcd(a,b) = \zero$, then $a = b = \zero$.
5. If $\ndiv(a,b)$, then $\ndiv(\ngcd(a,c),\ngcd(b,c))$.
6. If $\ndiv(c,a)$ and $\ndiv(c,b)$, then $$\ngcd(\nquo(a,c),\nquo(b,c)) = \nquo(\ngcd(a,b),c).$$
</div>

<div class="proof"><p>
1. Let $h = \ngcd(\ngcd(a,b),c)$, $k = \ngcd(a,\ngcd(b,c))$, $u = \ngcd(a,b)$, and $v = \ngcd(b,c)$. First we show that $\ndiv(h,k)$. Note that $\ndiv(h,u)$, so that $\ndiv(h,a)$ and $\ndiv(h,b)$. Now $\ndiv(h,c)$, so that $\ndiv(h,v)$. Thus $\ndiv(h,k)$. The proof that $\ndiv(k,h)$ is similar; thus $h = k$ as claimed.
2. Certainly if $\ngcd(a,b) = a$, then $\ndiv(a,b)$. Suppose conversely that $\ndiv(a,b)$. We consider two cases: either $a = \zero$ or $a = \next(t)$ for some $t$. If $a = \zero$, then $b = \zero$, and we have $$\ngcd(a,b) = \zero = a$$ as claimed. Suppose now that $a = \next(t)$. Since $\ndiv(a,b)$, we have $$b = \ntimes(q,a) = \nplus(\ntimes(q,a),\zero)$$ for some $q$. Now $\nleq(\zero,t)$, and by the uniqueness of remainders by nonzero divisors, we have $\nrem(b,a) = \zero$. So we have
$$\begin{eqnarray*}
 &   & \ngcd(a,b) \\
 & = & \ngcd(b,a) \\
 & = & \ngcd(a,\nrem(b,a)) \\
 & = & \ngcd(a,\zero) \\
 & = & a
\end{eqnarray*}$$
as claimed.
3. We consider two cases: either $c = \zero$ or $c \neq \zero$. If $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \ntimes(\ngcd(a,b),c) \\
 & = & \zero \\
 & = & \ngcd(\zero,\zero) \\
 & = & \ngcd(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
as claimed. Now suppose $c \neq \zero$. First note that $\ndiv(\ngcd(a,b),a)$, so that $$\ndiv(\ntimes(\ngcd(a,b),c),\ntimes(a,c)).$$ Similarly, we have $$\ndiv(\ntimes(\ngcd(a,b),c),\ntimes(b,c)).$$ Thus $$\ndiv(\ntimes(\ngcd(a,b),c), \ngcd(\ntimes(a,c),\ntimes(b,c))).$$ Now note that $\ndiv(c,\ntimes(a,c))$ and $\ndiv(c,\ntimes(b,c))$, so that $$\ndiv(c,\ngcd(\ntimes(a,c),\ntimes(b,c))).$$ Say $$\ntimes(u,c) = \ngcd(\ntimes(a,c),\ntimes(b,c)).$$ Now $\ndiv(\ntimes(u,c),\ntimes(a,c))$, so that $\ndiv(u,a)$; similarly, $\ndiv(u,b)$. Thus $\ndiv(u,\ngcd(a,b))$, and we have $$\ndiv(\ngcd(\ntimes(a,c),\ntimes(b,c)),\ntimes(\ngcd(a,b),c)).$$ By the antisymmetry of $\ndiv$, we have $$\ngcd(\ntimes(a,c),\ntimes(b,c) = \ntimes(\ngcd(a,b),c)$$ as claimed.
4. We proceed by strong induction on $b$. For the base case $b = \zero$, note that $$a = \ngcd(a,\zero) = \zero$$ as claimed. Now suppose we have $n$ such that the implication holds for all $b$ with $\nleq(b,n)$, and that $b = \next(n)$. Now $$\zero = \ngcd(a,b) = \ngcd(b,\nrem(a,b)),$$ where $\nleq(\nrem(a,b),b)$. By the induction hypothesis we have $b = \zero$ and $\nrem(a,b) = \zero$, so that $$a = \nplus(\ntimes(\nquo(a,b),b),\nrem(a,b)) = \zero$$ as claimed.
5. Note that
$$\begin{eqnarray*}
 &   & \ngcd(\ngcd(a,c),\ngcd(b,c)) \\
 & = & \ngcd(\ngcd(a,b),\ngcd(c,c)) \\
 & = & \ngcd(a,c).
\end{eqnarray*}$$
Thus $\ndiv(\ngcd(a,c),\ngcd(b,c))$ as claimed.
6. We consider two cases: either $c = \zero$ or $c \neq \zero$. If $c = \zero$, then $\nquo(a,c) = \zero$ and $\nquo(b,c) = \zero$, so we have
$$\begin{eqnarray*}
 &   & \ngcd(\nquo(a,c),\nquo(b,c)) \\
 & = & \ngcd(\zero,\zero) \\
 & = & \zero \\
 & = & \nquo(\ngcd(a,b),c)
\end{eqnarray*}$$
as claimed. Suppose now that $c \neq \zero$. Say $a = \ntimes(c,u)$ and $b = \ntimes(c,v)$. Note that
$$\begin{eqnarray*}
 &   & \ntimes(c,\ngcd(u,v)) \\
 & = & \ngcd(\ntimes(c,u),\ntimes(c,v)) \\
 & = & \ngcd(a,b).
\end{eqnarray*}$$
By the uniqueness of quotients by nonzero divisors, $$\nquo(\ngcd(a,b),c) = \ngcd(\nquo(a,c),\nquo(b,c))$$ as claimed.
</p></div>
</div>


Implementation and Testing
--------------------------

Here's ``gcd``:

> gcd :: (Natural t) => t -> t -> t
> gcd a b = (bailoutRec phi beta psi omega) (next (plus a b)) (a,b)
>   where
>     phi     (_,b) = b
>     beta  _ (_,b) = isZero b
>     psi   _ (a,_) = a
>     omega _ (a,b) = (b, rem a b)

Property tests for ``gcd``:

> -- gcd(a,0) == a and gcd(0,a) == a
> _test_gcd_zero :: (Natural n)
>   => n -> Nat n -> Bool
> _test_gcd_zero _ a =
>   (a ==== gcd a zero) &&& (a ==== gcd zero a)
> 
> 
> -- gcd(a,next(0)) == next(0) and gcd(next(0),a) == next(0)
> _test_gcd_one :: (Natural n)
>   => n -> Nat n -> Bool
> _test_gcd_one _ a = and
>   ((next zero) ==== gcd a (next zero))
>   ((next zero) ==== gcd (next zero) a)
> 
> 
> -- gcd(a,b) == gcd(b,rem(a,b))
> _test_gcd_rem :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_gcd_rem _ a b =
>   (gcd a b) ==== (gcd b (rem a b))
> 
> 
> -- gcd(a,b) == gcd(b,a)
> _test_gcd_commutative :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_gcd_commutative _ a b =
>   (gcd a b) ==== (gcd b a)
> 
> 
> -- div(gcd(a,b),a) and div(gcd(a,b),b)
> _test_gcd_div_args :: (Natural n)
>   => n -> Nat n -> Nat n -> Bool
> _test_gcd_div_args _ a b =
>   (div (gcd a b) a) &&& (div (gcd a b) b)
> 
> 
> -- gcd(a,a) = a
> _test_gcd_idempotent :: (Natural n)
>   => n -> Nat n -> Bool
> _test_gcd_idempotent _ a =
>   (gcd a a) ==== a
> 
> 
> -- gcd(gcd(a,b),c) == gcd(a,gcd(b,c))
> _test_gcd_associative :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_gcd_associative _ a b c =
>   (gcd (gcd a b) c) ==== (gcd a (gcd b c))
> 
> 
> -- times(gcd(a,b),c) == gcd(times(a,c),times(b,c))
> _test_gcd_distributive_times :: (Natural n)
>   => n -> Nat n -> Nat n -> Nat n -> Bool
> _test_gcd_distributive_times _ a b c =
>   (times (gcd a b) c) ==== (gcd (times a c) (times b c))

And the suite:

> -- run all tests for gcd
> _test_gcd :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_gcd t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_gcd_zero t)
>   , quickCheckWith args (_test_gcd_one t)
>   , quickCheckWith args (_test_gcd_rem t)
>   , quickCheckWith args (_test_gcd_commutative t)
>   , quickCheckWith args (_test_gcd_div_args t)
>   , quickCheckWith args (_test_gcd_idempotent t)
>   , quickCheckWith args (_test_gcd_associative t)
>   , quickCheckWith args (_test_gcd_distributive_times t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

> main_gcd :: IO ()
> main_gcd = _test_gcd (zero :: Unary) 20 100
