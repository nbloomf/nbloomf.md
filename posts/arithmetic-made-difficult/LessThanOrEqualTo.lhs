---
title: Less Than or Equal To
author: nbloomf
date: 2017-04-05
tags: arithmetic-made-difficult, literate-haskell
slug: leq
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module LessThanOrEqualTo
>  ( leq, _test_leq, main_leq
>  ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import DisjointUnions
> import NaturalNumbers
> import Plus
> import Times
> import Minus

Next we'd like to nail down what it means for one natural number to be less than or equal to another. Note that while $\nplus$ and $\ntimes$ have signatures $$\nats \times \nats \rightarrow \nats,$$ "less than or equal to" (which I will abbrebiate to *leq* from now on) does not. In fact relations like this are typically defined as a set of pairs. To make "less than" computable, we will instead (try to) define it as a function with signature $$\nats \times \nats \rightarrow \bool.$$ In fact, we can make a reasonable attempt on $\nleq$ without using (explicit) recursion at all.

:::::: definition ::
[]{#dfn-leq}
Define $\nleq : \nats \times \nats \rightarrow \bool$ by $$\nleq(a,b) = \isRgt(\nminus(b,a)).$$

In Haskell:

> leq :: (Natural n) => n -> n -> Bool
> leq a b = isRgt (minus b a)

::::::::::::::::::::

First some basic (but important!) special cases.

:::::: theorem :::::
[]{#thm-leq-next-zero}[]{#thm-leq-next-next-one}[]{#thm-leq-next-nat}[]{#thm-leq-nat-plus}
Let $a,b \in \nats$. Then we have the following.

1. $\nleq(\next(a),\zero) = \bfalse$.
2. $\nleq(\next(\next(a)),\next(\zero)) = \bfalse$.
3. $\nleq(\next(a),a) = \bfalse$.
4. $\nleq(a,\nplus(a,b)) = \btrue$.

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \nleq(\next(a),\zero) \\
 &     \href{@leq@#dfn-leq}
   = & \isRgt(\nminus(\zero,\next(a))) \\
 &     \href{@minus@#thm-minus-zero-next}
   = & \isRgt(\lft(\ast)) \\
 &     \href{@disjoint-unions@#thm-isRgt-lft}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \nleq(\next(\next(a)),\next(\zero)) \\
 &     \href{@leq@#dfn-leq}
   = & \isRgt(\nminus(\next(\zero),\next(\next(a)))) \\
 &     \href{@minus@#thm-minus-next-cancel}
   = & \isRgt(\nminus(\zero,\next(a))) \\
 &     \href{@minus@#thm-minus-zero-next}
   = & \isRgt(\lft(\ast)) \\
 &     \href{@disjoint-unions@#thm-isRgt-lft}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \nleq(\next(a),a) \\
 &     \href{@leq@#dfn-leq}
   = & \isRgt(\nminus(a,\next(a))) \\
 &     \href{@minus@#thm-minus-next-self}
   = & \isRgt(\lft(\ast)) \\
 &     \href{@disjoint-unions@#thm-isRgt-lft}
   = & \bfalse
\end{eqnarray*}$$
as claimed.
4. We have $\nminus(\nplus(a,b),a) = \rgt(b)$, so $\nleq(a,\nplus(a,b)) = \btrue$.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_next_nat_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_leq_next_nat_zero _ =
>   testName "leq(next(a),zero) == false" $
>   \a -> eq (leq (next a) zero) false
> 
> 
> _test_leq_next_next_nat_one :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_leq_next_next_nat_one _ =
>   testName "leq(next(next(a)),next(zero)) == false" $
>   \a -> eq (leq (next (next a)) (next zero)) false
> 
> 
> _test_leq_next_nat :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_leq_next_nat _ =
>   testName "leq(next(a),a) == false" $
>   \a -> eq (leq (next a) a) false
> 
> 
> _test_leq_right_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_right_plus _ =
>   testName "leq(a,plus(a,b)) == true" $
>   \a b -> eq (leq a (plus a b)) true

::::::::::::::::::::
::::::::::::::::::::

This lemma will also come in handy.

:::::: theorem :::::
[]{#thm-leq-next-cancel}
For all $a,b \in \nats$ we have $\nleq(\next(a),\next(b)) = \nleq(a,b)$.

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \nleq(\next(a),\next(b)) \\
 &     \href{@leq@#dfn-leq}
   = & \isRgt(\nminus(\next(b),\next(a))) \\
 &     \href{@minus@#thm-minus-next-cancel}
   = & \isRgt(\nminus(b,a)) \\
 &     \href{@leq@#dfn-leq}
   = & \nleq(a,b)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_next_cancel :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_next_cancel _ =
>   testName "leq(next(a),next(b)) == leq(a,b)" $
>   \a b -> eq (leq (next a) (next b)) (leq a b)

::::::::::::::::::::
::::::::::::::::::::

We can characterize $\nleq(a,b)$ in terms of the solubility of the equation $b = \nplus(a,x)$ as follows.

:::::: theorem :::::
Let $a,b \in \nats$. Then $\nleq(a,b) = \btrue$ if and only if there exists a $c \in \nats$ such that $b = \nplus(a,c)$.

::: proof ::::::::::
We have $\nleq(a,b) = \btrue$ if and only if $\nminus(b,a) = \rgt(c)$ for some $c \in \nats$, if and only if $b = \nplus(a,c)$ for some $c \in \nats$.
::::::::::::::::::::
::::::::::::::::::::

From here we can more easily prove some familiar properties of $\nleq$.

:::::: theorem :::::
[]{#thm-leq-reflexive}[]{#thm-leq-antisymmetric}[]{#thm-leq-transitive}
We have the following.

1. (Reflexivity) Let $a \in \nats$. Then $\nleq(a,a)$.
2. (Antisymmetry) Let $a,b \in \nats$. If $\nleq(a,b)$ and $\nleq(b,a)$, then $a = b$.
3. (Transitivity) Let $a,b,c \in \nats$. If $\nleq(a,b)$ and $\nleq(b,c)$, then $\nleq(a,c)$.

::: proof ::::::::::
1. We have $a = \nplus(a,\zero)$, so that $\nminus(a,a) = \zero$, thus $\nleq(a,a) = \btrue$.
2. Suppose $\nleq(a,b)$ and $\nleq(b,a)$; then there exist $u,v \in \nats$ such that $b = \nplus(a,u)$ and $a = \nplus(b,v)$. Now
$$\begin{eqnarray*}
 &   & \nplus(a,\zero) \\
 &     \href{@plus@#thm-plus-zero-right}
   = & a \\
 & = & \nplus(b,v) \\
 & = & \nplus(\nplus(a,u),v) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(a,\nplus(u,v))
\end{eqnarray*}$$
so that $\zero = \nplus(u,v)$, and thus $u = v = \zero$. So $b = \nplus(a,\zero) = a$ as claimed.
3. Suppose $\nleq(a,b)$ and $\nleq(b,c)$; then there exist $u,v \in \nats$ such that $b = \nplus(a,u)$ and $c = \nplus(b,v)$. Now
$$\begin{eqnarray*}
 &   & c \\
 & = & \nplus(b,v) \\
 & = & \nplus(\nplus(a,u),v) \\
 &     \href{@plus@#thm-plus-associative}
   = & \nplus(a,\nplus(u,v))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_reflexive :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_leq_reflexive _ =
>   testName "leq(a,a) == true" $
>   \a -> eq (leq a a) true
> 
> 
> _test_leq_antisymmetric :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_antisymmetric _ =
>   testName "if and(leq(a,b),leq(b,a)) then eq(a,b)" $
>   \a b -> if and (leq a b) (leq b a)
>     then eq a b
>     else true
> 
> 
> _test_leq_transitive :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_leq_transitive _ =
>   testName "if and(leq(a,b),leq(b,c)) then leq(a,c)" $
>   \a b c -> if and (leq a b) (leq b c)
>     then leq a c
>     else true

::::::::::::::::::::
::::::::::::::::::::

Now $\nleq$ interacts nicely with $\nplus$.

:::::: theorem :::::
[]{#thm-leq-plus-compatible-right}[]{#thm-leq-plus-compatible-left}
The following hold for all $a,b,c,d \in \nats$.

1. $\nleq(a,b) = \nleq(\nplus(a,c),\nplus(b,c))$.
2. $\nleq(a,b) = \nleq(\nplus(c,a),\nplus(c,b))$.
3. If $\nleq(a,b)$ and $\nleq(c,d)$, then $\nleq(\nplus(a,c),\nplus(b,d))$.

::: proof ::::::::::
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\nplus(a,\zero),\nplus(b,\zero)) = \nleq(a,b)$$ as needed. For the inductive step, suppose the result holds for some $c$. Now
$$\begin{eqnarray*}
 &   & \nleq(\nplus(a,\next(c)),\nplus(b,\next(c))) \\
 & = & \nleq(\nplus(\next(a),c),\nplus(\next(b),c)) \\
 &     \href{@leq@#thm-leq-plus-compatible-right}
   = & \nleq(\next(a),\next(b)) \\
 &     \href{@leq@#thm-leq-next-cancel}
   = & \nleq(a,b)
\end{eqnarray*}$$
as needed.
2. We have $$\nleq(\nplus(c,a),\nplus(c,b)) = \nleq(\nplus(a,c),\nplus(b,c)) = \nleq(a,b).$$
3. We have $$\btrue = \nleq(a,b) = \nleq(\nplus(a,c),\nplus(b,c))$$ and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(c,d) \\
 &     \href{@leq@#thm-leq-plus-compatible-right}
   = & \nleq(\nplus(c,b),\nplus(d,b)) \\
 & = & \nleq(\nplus(b,c),\nplus(b,d)).
\end{eqnarray*}$$
The result holds by transitivity.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_plus_nat_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_leq_plus_nat_right _ =
>   testName "leq(a,b) == leq(plus(a,c),plus(b,c))" $
>   \a b c -> eq (leq a b) (leq (plus a c) (plus b c))
> 
> 
> _test_leq_plus_nat_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_leq_plus_nat_left _ =
>   testName "leq(a,b) == leq(plus(c,a),plus(c,b))" $
>   \a b c -> eq (leq a b) (leq (plus c a) (plus c b))
> 
> 
> _test_leq_plus_compatible :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> n -> Bool)
> _test_leq_plus_compatible _ =
>   testName "if and(leq(a,b),leq(c,d)) then leq(plus(a,c),plus(b,d))" $
>   \a b c d -> if and (leq a b) (leq c d)
>     then leq (plus a c) (plus b d)
>     else true

::::::::::::::::::::
::::::::::::::::::::

We can perform case analysis using $\nleq$.

:::::: theorem :::::
The following hold for all $a,b \in \nats$.

1. If $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true.
2. Precisely one of the following is true: (i) $a = b$, (ii) $a \neq b$ and $\nleq(a,b)$, and (iii) $a \neq b$ and $\nleq(b,a)$.
3. If $\nleq(a,\next(b))$, then either $\nleq(a,b)$ or $a = \next(b)$.
4. If $\nleq(b,a)$ and $\nleq(a,\next(b))$, then either $a = b$ or $a = \next(b)$.

::: proof ::::::::::
1. If $\nleq(a,b)$ is false, we have $\nminus(b,a) = \lft(\ast)$. Now $\nminus(a,b) \rgt(c)$ for some $c$, so that $\nminus(b,a)$ is true.
2. If $a \neq b$ and $\nleq(a,b)$ is false, then $\nleq(b,a)$ is true. If $a \neq b$ and both $\nleq(a,b)$ and $\nleq(b,a)$, then $a = b$, which is absurd.
3. Say $\next(b) = \nplus(a,c)$. If $c = \zero$, we have $a = \next(b)$. If $c = \next(d)$, we have $$\next(b) = \nplus(a,\next(d)) = \next(\nplus(a,d))$$ so that $b = \nplus(a,d)$ and thus $\nleq(a,b)$.
4. By (3), either $a = \next(b)$ or $\nleq(a,b)$; if $\nleq(a,b)$, then by antisymmetry we have $a = b$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_swap_false :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_swap_false _ =
>   testName "if not(leq(a,b)) then leq(b,a)" $
>   \a b -> if not (leq a b)
>     then leq b a
>     else true
> 
> 
> _test_leq_trichotomy :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_trichotomy _ =
>   testName "or(eq(a,b),or(leq(a,b),leq(b,a)))" $
>   \a b -> or (eq a b) (or (leq a b) (leq b a))
> 
> 
> _test_leq_next_dichotomy :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_next_dichotomy _ =
>   testName "if leq(a,next(b)) then or(leq(a,b),eq(a,next(b)))" $
>   \a b -> if leq a (next b)
>     then or (leq a b) (eq a (next b))
>     else true
> 
> 
> _test_leq_next_squeeze :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_leq_next_squeeze _ =
>   testName "if and(leq(b,a),leq(a,next(b))) then or(eq(a,b),eq(a,next(b)))" $
>   \a b -> if and (leq b a) (leq a (next b))
>     then or (eq a b) (eq a (next b))
>     else true

::::::::::::::::::::
::::::::::::::::::::

And here comes $\ntimes$:

:::::: theorem :::::
The following hold for all $a,b,c,d \in \nats$.

1. $\nleq(a,b) = \nleq(\ntimes(a,\next(c)),\nplus(b,\next(c)))$.
2. Let $a,b,c,d \in \nats$. If $\nleq(a,b)$ and $\nleq(c,d)$, then $\nleq(\ntimes(a,c),\ntimes(b,d))$.

::: proof ::::::::::
1. We proceed by induction on $c$. For the base case, note that $$\nleq(\ntimes(a,\next(\zero)),\ntimes(b,\next(\zero))) = \nleq(a,b).$$ For the inductive step, suppose the result holds for some $c$. We consider three possibilities. First suppose $a = b$; in this case we have $\nleq(a,b) = \btrue$ and $$\ntimes(a,\next(\next(c))) = \ntimes(b,\next(\next(c))),$$ so the conclusion holds. Next, suppose $a \neq b$ and $\nleq(a,b) = \btrue$. By the inductive hypothesis we have $$\nleq(\ntimes(a,\next(c)),\nplus(b,\next(c))) = \btrue,$$ and so
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\nplus(\ntimes(a,\next(c)),a),\nplus(\ntimes(b,\next(c)),b)) \\
 & = & \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c))))
\end{eqnarray*}$$
as needed. Finally, suppose $a \neq b$ and $\nleq(a,b)$ is false. Then $\nleq(b,a)$ is true, and by the prior argument we have $$\nleq(b,a) = \nleq(\ntimes(a,\next(\next(c))),\ntimes(b,\next(\next(c)))).$$ Note that $$\ntimes(a,\next(\next(c))) \neq \ntimes(b,\next(\next(c)))$$ (since $a \neq b$). So we have $$\nleq(\ntimes(a,\next(\next(c))),\nplus(b,\next(\next(c))))$$ as needed.
2. There are two possibilities for $c$. If $c = \zero$, then we have
$$\begin{eqnarray*}
 &   & \nleq(\ntimes(a,c),\ntimes(b,d)) \\
 & = & \nleq(\zero,\ntimes(b,d)) \\
 & = & \btrue
\end{eqnarray*}$$
Suppose instead that $c = \next(u)$. Now there are two possibilities for $b$. If $b = \zero$, then in fact $a = \zero$, and we have
$$\begin{eqnarray*}
 &   & \nleq(\ntimes(a,c),\ntimes(b,d)) \\
 & = & \nleq(\zero,\zero) \\
 &     \href{@leq@#thm-leq-reflexive}
   = & \btrue
\end{eqnarray*}$$
as needed. Suppose then that $b = \next(v)$. Now we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\ntimes(a,\next(u)),\ntimes(b,\next(u))) \\
 & = & \nleq(\ntimes(a,c),\ntimes(b,c))
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \nleq(\ntimes(c,\next(v)),\ntimes(d,\next(v))) \\
 & = & \nleq(\ntimes(b,c),\ntimes(b,d)).
\end{eqnarray*}$$
The conclusion holds by transitivity.
::::::::::::::::::::

::: test :::::::::::

> _test_leq_times_compatible :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_leq_times_compatible _ =
>   testName "leq(a,b) == leq(times(a,next(c)),times(b,next(c)))" $
>   \a b c -> eq (leq a b) (leq (times a (next c)) (times b (next c)))

::::::::::::::::::::
::::::::::::::::::::

That's enough.


Testing
-------

Suite:

> _test_leq :: (TypeName n, Natural n, Equal n, Arbitrary n, Show n)
>   => n -> Int -> Int -> IO ()
> _test_leq n size cases = do
>   testLabel1 "leq" n
> 
>   let
~ args = testArgs size cases
> 
>   runTest args (_test_leq_next_nat_zero n)
>   runTest args (_test_leq_next_next_nat_one n)
>   runTest args (_test_leq_next_nat n)
>   runTest args (_test_leq_right_plus n)
>   runTest args (_test_leq_next_cancel n)
>   runTest args (_test_leq_reflexive n)
>   runTest args (_test_leq_antisymmetric n)
>   runTest args (_test_leq_transitive n)
>   runTest args (_test_leq_plus_nat_right n)
>   runTest args (_test_leq_plus_nat_left n)
>   runTest args (_test_leq_plus_compatible n)
>   runTest args (_test_leq_swap_false n)
>   runTest args (_test_leq_trichotomy n)
>   runTest args (_test_leq_next_dichotomy n)
>   runTest args (_test_leq_next_squeeze n)
>   runTest args (_test_leq_times_compatible n)

Main:

> main_leq :: IO ()
> main_leq = do
>   _test_leq (zero :: Unary) 50 100
