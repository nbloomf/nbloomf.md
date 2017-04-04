---
title: Less Than or Equal To
author: nbloomf
date: 2017-04-02
tags: arithmetic-made-difficult, literate-haskell
---

> module LessThanOrEqualTo
>  ( leq, _test_leq
>  ) where
> 
> import NaturalNumbers
> import Plus
> import Times
> 
> import Test.QuickCheck

Next we'd like to nail down what it means for one natural number to be less than or equal to another. Note that while $\nplus$ and $\ntimes$ have signatures $$\nats \times \nats \rightarrow \nats,$$ "less than or equal to" (which I will abbrebiate to *leq* from now on) does not. In fact $\leq$ is typically defined as a set of pairs. To make $\leq$ computable, we will instead (try to) define it as a function with signature $$\nats \times \nats \rightarrow \bool.$$ With this signature there is hope that we can define leq using primitive recursion, provided we can find appropriate maps $$\varphi : \nats \rightarrow \bool$$ and $$\mu : \nats \times \nats \times \bool \rightarrow \bool.$$ But what should $\varphi$ and $\mu$ be? Let's think about it.

One nice thing about $\primrec{\ast}{\ast}$ (and recursion operators in general) is that we can afford to be a little sloppy while looking for a good definition.

Let $\Theta = \primrec{\varphi}{\mu}$, and suppose $\Theta$ acts like the $\leq$ we know and love. Then for all $b$ we want, for instance, $$\btrue = \Theta(\zero,b) = \varphi(b);$$ evidently then we should have $\varphi(b) = \btrue$ for all $b$. Likewise, we have $$\Theta(\next(a),b) = \mu(a,b,\Theta(a,b)).$$ That is, the truth value of $a+1 \leq b$ is some function of $a$, $b$, and the truth value of $a \leq b$. Note that if $a = b$, then $a+1 \leq b$ is *false*. If $a > b$, then $a \leq b$ and $a+1 \leq b$ are both false, and if $a < b$, then $a \leq b$ and $a+1 \leq b$ are both true. So let's try $\mu(a,b,k) = \bfalse$ if $a = b$ and $k$ otherwise.

<div class="result">
<div class="defn"><p>
Let $\mu : \nats \times \nats \times \bool \rightarrow \bool$ be given by $$\mu(a,b,k) = \left\{ \begin{array}{ll} \bfalse & \mathrm{if}\ a = b \\ k & \mathrm{otherwise}, \end{array} \right.$$ and define $\varphi : \nats \rightarrow \bool$ by $\varphi(x) = \btrue$. We then define $\nleq : \nats \times \nats \rightarrow \bool$ by $$\nleq = \primrec{\varphi}{\mu}.$$
</p></div>
</div>

First a basic (but important!) lemma.

<div class="result">
<div class="lemma">
Let $a \in \nats$. Then we have the following.

1. $\nleq(\next(a),\zero) = \bfalse$.
2. $\nleq(\next(\next(a)),\next(\zero)) = \bfalse$.
</div>

<div class="proof"><p>
1. We induct on $a$. For the base case, note that $\nleq(\next(\zero),\zero)$ is false since $\zero = \zero$. For the inductive step, suppose we have that $\nleq(\next(a),\zero)$ is false. Now $\nleq(\next(\next(a)),\zero)$ has the same value as $\nleq(\next(a),\zero)$ (false) since $\next(a) \neq \zero$.
2. We induct on $a$. For the base case, note that $\nleq(\next(\next(\zero)),\next(\zero)) = \bfalse$ since $\next(\zero) = \next(\zero)$. For the inductive step, suppose $$\nleq(\next(\next(a)),\next(\zero)) = \bfalse.$$ Now $$\nleq(\next(\next(\next(a)),\next(\zero))$$ has the same value as $$\nleq(\next(\next(a)),\next(\zero))$$ (false) since $\next(\next(a)) \neq \next(\zero)$.
</p></div>
</div>

This lemma will also come in handy.

<div class="result">
<div class="lemma">
For all $a,b \in \nats$, if $\nleq(\next(a),\next(b)) = \btrue$ then $\nleq(a,b) = \btrue$.
</div>

<div class="proof"><p>
Let $$A = \{ a \in \nats \mid \forall b \in \nats,\ \mathrm{if}\ \nleq(\next(a),\next(b))\ \mathrm{then}\ \nleq(a,b) \}.$$ We show that $A = \nats$ by induction. For the base case, suppose we have $\nleq(\next(\zero),\next(b))$. Now $\nleq(\zero,b)$ is true by definition.

For the inductive step, given $x \in \nats$ define $$B(x) = \{ b \in \nats \mid \mathrm{if}\ \nleq(\next(x),\next(b))\ \mathrm{then}\ \nleq(x,b) \}.$$ The inductive hypothesis is that $B(a) = \nats$, and we wish to show that $B(\next(a)) = \nats$; we show this by induction. For the base case, note that $\nleq(\next(\next(a)),\next(\zero))$ is false, so that $\zero \in B(\next(a))$ vacuously.

For the inductive step, suppose we have $b \in B(\next(a))$ and assume that $$\nleq(\next(\next(a)),\next(\next(b))) = \btrue.$$ Now we must have $\next(a) \neq \next(\next(b))$, so that $a \neq \next(b)$. Moreover we have $\nleq(\next(a),\next(\next(b))) = \btrue$. By the inductive hypothesis we have $\nleq(a,\next(b))$. And because $a \neq \next(b)$, we have $\nleq(\next(a),\next(b))$ as needed. So $\next(b) \in B(\next(a))$, and thus $B(\next(a)) = \nats$, so that $\next(a) \in A$, and thus $A = \nats$ as claimed.
</p></div>
</div>

We can characterize $\nleq(a,b)$ in terms of the solubility of the equation $b = \nplus(a,x)$ as follows.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\nleq(a,b) = \btrue$ if and only if there exists a $c \in \nats$ such that $b = \nplus(a,c)$.
</div>

<div class="proof"><p>
First we show that for all $a,b \in \nats$, if $\nleq(a,b)$ then we have $b = \nplus(a,c)$ for some $c \in \nats$. To this end, define $$A = \{ a \in \nats \mid \forall b \in \nats,\ \mathrm{if}\ \nleq(a,b)\ \mathrm{then}\ \exists c \in \nats. b = \nplus(a,c) \}.$$ We will show that $A = \nats$ by induction.

For the base case, note that if $b \in \nats$ we have $\nleq(\zero,b)$ is true and $b = \nplus(\zero,b)$. So we have $\zero \in A$.

For the inductive step, suppose we have $a \in A$. Now define (for any $x \in \nats$) the set $$B(x) = \{ b \in \nats \mid \mathrm{if}\ \nleq(x,b)\ \mathrm{then}\ \exists c \in \nats. b = \nplus(x,c) \}.$$ By the induction hypothesis we have $B(a) = \nats$, and if $B(\next(a)) = \nats$, then $\next(a) \in A$; we will show this by induction.

For the base case note that $\nleq(\next(a),\zero)$ is false, so that $\zero \in B(\next(a))$ vacuously.

For the inductive step, suppose $b \in B(\next(a))$ and that $\nleq(\next(a),\next(b))$ is true. In particular, unpacking the definition of $\nleq$ we have $a \neq \next(b)$ (since in this case $\nleq(\next(a),\next(b))$ is false) and $\nleq(a,\next(b))$ is true. Now $a \in A$, so we have $d \in \nats$ such that $\next(b) = \nplus(a,d)$. And because $a \neq \next(b)$, we also have $d = \next(c)$ for some $c \in \nats$. Now $$\next(b) = \nplus(a,\next(c)) = \nplus(\next(a),c).$$ Thus $\next(b) \in B(\next(a))$, and by induction $B(\next(a)) = \nats$, so that $\next(a) \in A$. By induction $A = \nats$ and this half of the theorem is proved.

Next we show that if $b = \nplus(a,c)$ then $\nleq(a,b)$ is true; for this it suffices to show that $\nleq(a,\nplus(a,b))$ is true for all $a,b \in \nats$. We show this by induction; to this end let $$A = \{ a \in \nats \mid \forall b \in \nats, \nleq(a,\nplus(a,b)) = \btrue \}.$$ For the base case, note that if $b \in \nats$ we have $\nleq(\zero,\nplus(\zero,b)) = \nleq(\zero,b) = \btrue$; thus $\zero \in A$.

For the inductive step, suppose we have $a \in A$. Note that $a \neq \nplus(\next(a),b)$, since otherwise we have $\zero = \next(b)$. Note also that $\nleq(a,\nplus(\next(a),b)) = \nleq(a,\nplus(a,\next(b))) = \btrue$ by the induction hypothesis. Thus $\nleq(\next(a),\nplus(\next(a),b))$ as needed.
</p></div>
</div>

From here we can more easily prove some familiar properties of $\nleq$.

<div class="result">
<div class="thm">
We have the following.

1. (Reflexivity) Let $a \in \nats$. Then $\nleq(a,a)$.
2. (Antisymmetry) Let $a,b \in \nats$. If $\nleq(a,b)$ and $\nleq(b,a)$, then $a = b$.
3. (Transitivity) Let $a,b,c \in \nats$. If $\nleq(a,b)$ and $\nleq(b,c)$, then $\nleq(a,c)$.
</div>

<div class="proof"><p>
1. We have $a = \nplus(a,\zero)$, so that $\nleq(a,a) = \btrue$.
2. Suppose $\nleq(a,b)$ and $\nleq(b,a)$; then there exist $u,v \in \nats$ such that $b = \nplus(a,u)$ and $a = \nplus(b,v)$. Now $$\begin{eqnarray*} & & \nplus(a,\zero) \\ & = & a \\ & = & \nplus(b,v) \\ & = & \nplus(\nplus(a,u),v) \\ & = & \nplus(a,\nplus(u,v)), \end{eqnarray*}$$ so that $\zero = \nplus(u,v)$, and thus $u = v = \zero$. So $b = \nplus(a,\zero) = a$ as claimed.
3. Suppose $\nleq(a,b)$ and $\nleq(b,c)$; then there exist $u,v \in \nats$ such that $b = \nplus(a,u)$ and $c = \nplus(b,v)$. Now $$\begin{eqnarray*} & & c \\ & = & \nplus(b,v) \\ & = & \nplus(\nplus(a,u),v) \\ & = & \nplus(a,\nplus(u,v)) \end{eqnarray*}$$ as needed.
</p></div>
</div>

And $\nleq$ interacts nicely with $\nplus$.

<div class="result">
<div class="thm">
The following hold.

1. Let $a,b,c \in \nats$. Then $\nleq(a,b) = \nleq(\nplus(a,c),\nplus(b,c))$.
2. Let $a,b,c,d \in \nats$. If $\nleq(a,b)$ and $\nleq(c,d)$, then $\nleq(\nplus(a,c),\nplus(b,d))$.
</div>

<div class="proof"><p>
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\nplus(a,\zero),\nplus(b,\zero)) = \nleq(a,b)$$ as needed. For the inductive step, suppose the result holds for some $c$. Now $$\begin{eqnarray*} & & \nleq(\nplus(a,\next(c)),\nplus(b,\next(c))) \\ & = & \nleq(\nplus(\next(a),c),\nplus(\next(b),c)) \\ & = & \nleq(\next(a),\next(b)) \\ & = & \nleq(a,b) \end{eqnarray*}$$ as needed.

2. We have $$\btrue = \nleq(a,b) = \nleq(\nplus(a,c),\nplus(b,c))$$ and $$\begin{eqnarray*} & & \btrue \\ & = & \nleq(c,d) \\ & = & \nleq(\nplus(c,b),\nplus(d,b)) \\ & = & \nleq(\nplus(b,c),\nplus(d,b)). \end{eqnarray*}$$ The result holds by transitivity.
</p></div>
</div>

We can perform case analysis using $\nleq$:

<div class="result">
<div class="thm">
The following hold for all $a,b \in \nats$.

1. If $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true.
2. Precisely one of the following is true: (i) $a = b$, (ii) $a \neq b$ and $\nleq(a,b)$, and (iii) $a \neq b$ and $\nleq(b,a)$.
</div>

<div class="proof"><p>
1. We proceed by induction on $a$. In the base case, the hypothesis $\nleq(\zero,b) = \bfalse$ is not true for any $b \in \nats$, so the implication holds vacuously. For the inductive step suppose the implication holds for some $a$. Suppose further that $\nleq(\next(a),b)$ is false. There are two possibilities: if $a = b$, then $\nleq(b,a)$ is true. If $a \neq b$, then we must have that $\nleq(a,b)$ is false; by the induction hypothesis, $\nleq(b,a)$ is true. Since $\nleq(\zero,\next(\zero))$, we have $\nleq(b,\next(a))$ as needed.
2. If $a \neq b$ and $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true.
</p></div>
</div>

And here comes $\ntimes$:

<div class="result">
<div class="thm">
The following hold.

1. Let $a,b,c \in \nats$. Then $$\nleq(a,b) = \nleq(\ntimes(a,\next(c)),\nplus(b,\next(c))).$$
2. Let $a,b,c,d \in \nats$. If $\nleq(a,b)$ and $\nleq(c,d)$, then $$\nleq(\ntimes(a,c),\ntimes(b,d)).$$
</div>

<div class="proof"><p>
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\ntimes(a,\next(\zero)),\ntimes(b,\next(\zero))) = \nleq(a,b).$$ For the inductive step, suppose the result holds for some $c$. We consider three possibilities. First suppose $a = b$; in this case we have $\nleq(a,b) = \btrue$ and $$\ntimes(a,\next(\next(c))) = \ntimes(a,\next(\next(c))),$$ so the conclusion holds. Next, suppose $a \neq b$ and $\nleq(a,b) = \btrue$. By the inductive hypothesis we have $$\nleq(\ntimes(a,\next(c)),\nplus(b,\next(c))) = \btrue,$$ and so $$\begin{eqnarray*} & & \btrue \\ & = & \nleq(\nplus(\ntimes(a,\next(c)),a),\nplus(\ntimes(b,\next(c)),b)) \\ & = & \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c)))) \end{eqnarray*}$$ as needed. Finally, suppose $a \neq b$ and $\nleq(a,b)$ is false. Then $\nleq(b,a)$ is true, and by the prior argument we have $$\nleq(b,a) = \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c)))).$$ Note that $$\ntimes(a,\next(\next(c))) \neq \ntimes(b,\next(\next(c)))$$ (since $a \neq b$). So we have $$\nleq(\ntimes(a,\next(\next(c))),\nplus(b,\next(\next(c))))$$ as needed.
2. There are two possibilities for $c$. If $c = \zero$, then we have $$\begin{eqnarray*} & & \nleq(\ntimes(a,c),\ntimes(b,d)) \\ & = & \nleq(\zero,\ntimes(b,d)) \\ & = & \btrue \end{eqnarray*}.$$ Suppose instead that $c = \next(u)$. Now there are two possibilities for $b$. If $b = \zero$, then in fact $a = \zero$, and we have $$\begin{eqnarray*} & & \nleq(\ntimes(a,c),\ntimes(b,d)) \\ & = & \nleq(\zero,\zero) \\ & = & \btrue \end{eqnarray*}$$ as needed. Suppose then that $b = \next(v)$. Now we have $$\begin{eqnarray*} & & \btrue \\ & = & \nleq(\ntimes(a,\next(u)),\ntimes(b,\next(u)) \\ & = & \nleq(\ntimes(a,c),\ntimes(b,c)) \end{eqnarray*}$$ and $$\begin{eqnarray*} & & \btrue \\ & = & \nleq(\ntimes(c,\next(v)),\ntimes(d,\next(v))) \\ & = & \nleq(\ntimes(b,c),\ntimes(b,d)). \end{eqnarray*}$$ The conclusion holds by transitivity.
</p></div>
</div>

We can perform case analysis using $\nleq$:

<div class="result">
<div class="thm">
Let $a,b \in \nats$. If $\nleq(a,\next(b))$, then either $\nleq(a,b)$ or $a = \next(b)$.
</div>

<div class="proof"><p>
Say $\next(b) = \nplus(a,c)$. If $c = \zero$, we have $a = \next(b)$. If $c = \next(d)$, we have $$\next(b) = \nplus(a,\next(d)) = \next(\nplus(a,d))$$ so that $b = \nplus(a,d)$ and thus $\nleq(a,b)$.
</p></div>
</div>

That's enough.


Implementation and Testing
--------------------------

Here's ``leq``:

> leq :: (Natural t) => t -> t -> Bool
> leq = primitiveRec phi mu
>   where
>     phi _ = True
>     mu a b k = if a == b then False else k

And some property tests:

> -- leq(a,plus(a,b)) == True
> _test_leq_right_plus :: (Natural t) => t -> t -> t -> Bool
> _test_leq_right_plus _ a b =
>   (leq a (plus a b)) == True
> 
> 
> -- leq(a,a) == True
> _test_leq_reflexive :: (Natural t) => t -> t -> Bool
> _test_leq_reflexive _ a =
>   (leq a a) == True
> 
> 
> -- leq(a,b) == leq(plus(a,c),plus(b,c))
> _test_leq_plus :: (Natural t) => t -> t -> t -> t -> Bool
> _test_leq_plus _ a b c =
>   (leq a b) == (leq (plus a c) (plus b c))
> 
> 
> -- leq(a,b) == leq(times(a,next(c)),times(b,next(c)))
> _test_leq_times :: (Natural t) => t -> t -> t -> t -> Bool
> _test_leq_times _ a b c =
>   (leq a b) == (leq (times a (next c)) (times b (next c)))

And a test wrapper:

> -- run all tests for leq
> _test_leq :: (Natural t, Arbitrary t, Show t)
>   => t -> Int -> Int -> IO ()
> _test_leq t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_leq_reflexive t)
>   , quickCheckWith args (_test_leq_right_plus t)
>   , quickCheckWith args (_test_leq_plus t)
>   , quickCheckWith args (_test_leq_times t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
