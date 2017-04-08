---
title: Less Than or Equal To
author: nbloomf
date: 2017-04-05
tags: arithmetic-made-difficult, literate-haskell
---

> module LessThanOrEqualTo
>  ( leq, _test_leq
>  ) where
> 
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> 
> import Test.QuickCheck

Next we'd like to nail down what it means for one natural number to be less than or equal to another. Note that while $\nplus$ and $\ntimes$ have signatures $$\nats \times \nats \rightarrow \nats,$$ "less than or equal to" (which I will abbrebiate to *leq* from now on) does not. In fact $\leq$ is typically defined as a set of pairs. To make $\leq$ computable, we will instead (try to) define it as a function with signature $$\nats \times \nats \rightarrow \bool.$$ In fact, we can make a reasonable attempt on $\nleq$ without using recursion at all.

<div class="result">
<div class="defn"><p>
Define $\nleq : \nats \times \nats \rightarrow \bool$ by $$\nleq(a,b) = \left\{\begin{array}{ll} \bfalse & \mathrm{if}\ \nminus(b,a) = \ast \\ \btrue & \mathrm{otherwise}. \end{array}\right.$$
</p></div>
</div>

First a basic (but important!) special case.

<div class="result">
<div class="lemma">
Let $a \in \nats$. Then we have the following.

1. $\nleq(\next(a),\zero) = \bfalse$.
2. $\nleq(\next(\next(a)),\next(\zero)) = \bfalse$.
</div>

<div class="proof"><p>
1. Note that $$\zero = \nplus(\next(a),x) = \next(\nplus(a,x))$$ has no solution, so that $\nminus(\zero,\next(a)) = \ast$. Thus $\nleq(\next(a),\zero) = \bfalse$.
2. Note that $\nminus(\next(\next(a)),\next(\zero)) = \nminus(\next(a),\zero)$; the conclusion follows from (1).
</p></div>
</div>

This lemma will also come in handy.

<div class="result">
<div class="lemma">
For all $a,b \in \nats$ we have $\nleq(\next(a),\next(b)) = \nleq(a,b)$.
</div>

<div class="proof"><p>
Follows because $\nminus(\next(b),\next(a)) = \nminus(b,a)$.
</p></div>
</div>

We can characterize $\nleq(a,b)$ in terms of the solubility of the equation $b = \nplus(a,x)$ as follows.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then $\nleq(a,b) = \btrue$ if and only if there exists a $c \in \nats$ such that $b = \nplus(a,c)$.
</div>

<div class="proof"><p>
We have $\nleq(a,b) = \btrue$ if and only of $\nminus(b,a) = c \in \nats$, if and only if $b = \nplus(a,c)$.
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
1. We have $a = \nplus(a,\zero)$, so that $\nminus(a,a) = \zero$, thus $\nleq(a,a) = \btrue$.
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
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\nplus(a,\zero),\nplus(b,\zero)) = \nleq(a,b)$$ as needed. For the inductive step, suppose the result holds for some $c$. Now
$$\begin{eqnarray*}
 &   & \nleq(\nplus(a,\next(c)),\nplus(b,\next(c))) \\
 & = & \nleq(\nplus(\next(a),c),\nplus(\next(b),c)) \\
 & = & \nleq(\next(a),\next(b)) \\
 & = & \nleq(a,b)
\end{eqnarray*}$$
as needed.
2. We have $$\btrue = \nleq(a,b) = \nleq(\nplus(a,c),\nplus(b,c))$$ and $$\begin{eqnarray*} & & \btrue \\ & = & \nleq(c,d) \\ & = & \nleq(\nplus(c,b),\nplus(d,b)) \\ & = & \nleq(\nplus(b,c),\nplus(b,d)). \end{eqnarray*}$$ The result holds by transitivity.
</p></div>
</div>

We can perform case analysis using $\nleq$:

<div class="result">
<div class="thm">
The following hold for all $a,b \in \nats$.

1. If $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true.
2. Precisely one of the following is true: (i) $a = b$, (ii) $a \neq b$ and $\nleq(a,b)$, and (iii) $a \neq b$ and $\nleq(b,a)$.
3. Let $a,b \in \nats$. If $\nleq(a,\next(b))$, then either $\nleq(a,b)$ or $a = \next(b)$.
4. Let $a,b \in \nats$. If $\nleq(b,a)$ and $\nleq(a,\next(b))$, then either $a = b$ or $a = \next(b)$.
</div>

<div class="proof"><p>
1. If $\nleq(a,b)$ is false, we have $\nminus(b,a) = \ast$. Now $\nminus(a,b) \in \nats$, so that $\nminus(b,a)$ is true.
2. If $a \neq b$ and $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true.
3. Say $\next(b) = \nplus(a,c)$. If $c = \zero$, we have $a = \next(b)$. If $c = \next(d)$, we have $$\next(b) = \nplus(a,\next(d)) = \next(\nplus(a,d))$$ so that $b = \nplus(a,d)$ and thus $\nleq(a,b)$.
4. Use antisymmetry.
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
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\ntimes(a,\next(\zero)),\ntimes(b,\next(\zero))) = \nleq(a,b).$$ For the inductive step, suppose the result holds for some $c$. We consider three possibilities. First suppose $a = b$; in this case we have $\nleq(a,b) = \btrue$ and $$\ntimes(a,\next(\next(c))) = \ntimes(b,\next(\next(c))),$$ so the conclusion holds. Next, suppose $a \neq b$ and $\nleq(a,b) = \btrue$. By the inductive hypothesis we have $$\nleq(\ntimes(a,\next(c)),\nplus(b,\next(c))) = \btrue,$$ and so
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\nplus(\ntimes(a,\next(c)),a),\nplus(\ntimes(b,\next(c)),b)) \\
 & = & \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c))))
\end{eqnarray*}$$
as needed. Finally, suppose $a \neq b$ and $\nleq(a,b)$ is false. Then $\nleq(b,a)$ is true, and by the prior argument we have $$\nleq(b,a) = \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c)))).$$ Note that $$\ntimes(a,\next(\next(c))) \neq \ntimes(b,\next(\next(c)))$$ (since $a \neq b$). So we have $$\nleq(\ntimes(a,\next(\next(c))),\nplus(b,\next(\next(c))))$$ as needed.
2. There are two possibilities for $c$. If $c = \zero$, then we have $$\begin{eqnarray*} & & \nleq(\ntimes(a,c),\ntimes(b,d)) \\ & = & \nleq(\zero,\ntimes(b,d)) \\ & = & \btrue \end{eqnarray*}.$$ Suppose instead that $c = \next(u)$. Now there are two possibilities for $b$. If $b = \zero$, then in fact $a = \zero$, and we have $$\begin{eqnarray*} & & \nleq(\ntimes(a,c),\ntimes(b,d)) \\ & = & \nleq(\zero,\zero) \\ & = & \btrue \end{eqnarray*}$$ as needed. Suppose then that $b = \next(v)$. Now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\ntimes(a,\next(u)),\ntimes(b,\next(u)) \\
 & = & \nleq(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\ntimes(c,\next(v)),\ntimes(d,\next(v))) \\
 & = & \nleq(\ntimes(b,c),\ntimes(b,d)).
\end{eqnarray*}$$
The conclusion holds by transitivity.
</p></div>
</div>

That's enough.


Implementation and Testing
--------------------------

Here's ``leq``:

> leq :: (Natural t) => t -> t -> Bool
> leq a b = case minus b a of
>   Nothing -> False
>   Just _  -> True

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
