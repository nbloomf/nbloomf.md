---
title: Maximum and Minimum
author: nbloomf
date: 2017-04-07
tags: arithmetic-made-difficult, literate-haskell
slug: max-min
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module MaxAndMin
>   ( max, min, _test_max_min, main_max_min
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Plus
> import Times
> import Minus
> import LessThanOrEqualTo

With $\nleq$ in hand we can also define max and min functions. These are less interesting since they do not have to be defined recursively. :)

<div class="result">
<div class="defn"><p>
We define $\nmax : \nats \times \nats \rightarrow \nats$ by $$\nmax(a,b) = \bif{\nleq(a,b)}{b}{a}$$ and $\nmin : \nats \times \nats \rightarrow \nats$ by $$\nmin(a,b) = \bif{\nleq(a,b)}{a}{b}.$$

In Haskell:

> max :: (Natural n) => n -> n -> n
> max a b = if leq a b then b else a
> 
> min :: (Natural n) => n -> n -> n
> min a b = if leq a b then a else b

</p></div>
</div>

Special cases.

<div class="result">
<div class="thm">
Let $a \in \nats$. Then we have the following.

1. $\nmax(\zero,a) = a$.
2. $\nmax(a,a) = a$.
3. $\nmin(\zero,a) = \zero$.
4. $\nmin(a,a) = a$.
</div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \nmax(\zero,a) \\
 & = & \bif{\nleq(\zero,a)}{a}{\zero} \\
 & = & \bif{\btrue}{a}{\zero} \\
 & = & a
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \nmax(a,a) \\
 & = & \bif{\nleq(a,a)}{a}{a} \\
 & = & \bif{\btrue}{a}{a} \\
 & = & a
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \nmin(\zero,a) \\
 & = & \bif{\nleq(\zero,a)}{\zero}{a} \\
 & = & \bif{\btrue}{\zero}{a} \\
 & = & \zero
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \nmin(a,a) \\
 & = & \bif{\nleq(a,a)}{a}{a} \\
 & = & \bif{\btrue}{a}{a} \\
 & = & a
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_max_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_max_zero _ =
>   testName "a == max(a,0) and a == max(0,a)" $
>   \a -> and (eq a (max a zero)) (eq a (max zero a))
> 
> 
> _test_max_idempotent :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_max_idempotent _ =
>   testName "a == max(a,a)" $
>   \a -> eq (max a a) a
> 
> 
> _test_min_zero :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_min_zero _ =
>   testName "0 == min(a,0) and 0 == min(0,a)" $
>   \a -> and (eq zero (min a zero)) (eq zero (min zero a))
> 
> 
> _test_min_idempotent :: (Natural n, Equal n)
>   => n -> Test (n -> Bool)
> _test_min_idempotent _ =
>   testName "a == min(a,a)" $
>   \a -> eq (min a a) a

</p></div>
</div>

$\nmax$ and $\nmin$ are commutative.

<div class="result">
<div class="thm">
Let $a,b \in \nats$. Then we have the following.

1. $\nmax(a,b) = \nmax(b,a)$.
2. $\nmin(a,b) = \nmin(b,a)$.
</div>

<div class="proof"><p>
1. If $\nleq(a,b) = \bfalse, we have
$$\begin{eqnarray*}
 &   & \nmax(a,b) \\
 & = & \bif{\nleq(a,b)}{b}{a} \\
 & = & \bif{\not(\not(\nleq(a,b)))}{b}{a} \\
 & = & \bif{\nleq(b,a)}{a}{b} \\
 & = & \nmax(b,a)
\end{eqnarray*}$$
as claimed; similarly, if $\nleq(b,a) = \bfalse$ then $\nmax(a,b) = \nmax(b,a)$. Suppose then that $\nleq(a,b) = \nleq(b,a) = \btrue$. By antisymmetry we have $a = b$, and thus
$\nmax(a,b) = \nmax(b,a)$.
2. If $\nleq(a,b) = \bfalse, we have
$$\begin{eqnarray*}
 &   & \nmin(a,b) \\
 & = & \bif{\nleq(a,b)}{a}{b} \\
 & = & \bif{\not(\not(\nleq(a,b)))}{a}{b} \\
 & = & \bif{\nleq(b,a)}{b}{a} \\
 & = & \nmin(b,a)
\end{eqnarray*}$$
as claimed; similarly, if $\nleq(b,a) = \bfalse$ then $\nmin(a,b) = \nmin(b,a)$. Suppose then that $\nleq(a,b) = \nleq(b,a) = \btrue$. By antisymmetry we have $a = b$, and thus
$\nmin(a,b) = \nmin(b,a)$.
</p></div>

<div class="test"><p>

> _test_max_commutative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_max_commutative _ =
>   testName "max(a,b) == max(b,a)" $
>   \a b -> eq (max a b) (max b a)
> 
> 
> _test_min_commutative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_min_commutative _ =
>   testName "min(a,b) == min(b,a)" $
>   \a b -> eq (min a b) (min b a)

</p></div>
</div>

$\nplus$ and $\next$ distribute over $\nmax$ and $\nmin$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmax(\next(a),\next(b)) = \next(\nmax(a,b))$.
2. $\nmax(\nplus(c,a),\nplus(c,b)) = \nplus(c,\nmax(a,b))$.
3. $\nmin(\next(a),\next(b)) = \next(\nmin(a,b))$.
4. $\nmin(\nplus(c,a),\nplus(c,b)) = \nplus(c,\nmin(a,b))$.
</div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \nmax(\next(a),\next(b)) \\
 & = & \bif{\nleq(\next(a),\next(b))}{\next(b)}{\next(a)} \\
 & = & \bif{\nleq(a,b)}{\next(b)}{\next(a)} \\
 & = & \next(\bif{\nleq(a,b)}{b}{a}) \\
 & = & \next(\nmax(a,b))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \nmax(\nplus(c,a),\nplus(c,b)) \\
 & = & \bif{\nleq(\nplus(c,a),\nplus(c,b))}{\nplus(c,b)}{\nplus(c,a)} \\
 & = & \bif{\nleq(a,b)}{\nplus(c,b)}{\nplus(c,a)} \\
 & = & \nplus(c,\bif{\nleq(a,b)}{b}{a}) \\
 & = & \nplus(c,\nmax(a,b))
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \nmin(\next(a),\next(b)) \\
 & = & \bif{\nleq(\next(a),\next(b))}{\next(a)}{\next(b)} \\
 & = & \bif{\nleq(a,b)}{\next(a)}{\next(b)} \\
 & = & \next(\bif{\nleq(a,b)}{a}{b}) \\
 & = & \next(\nmin(a,b))
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \nmin(\nplus(c,a),\nplus(c,b)) \\
 & = & \bif{\nleq(\nplus(c,a),\nplus(c,b))}{\nplus(c,a)}{\nplus(c,b)} \\
 & = & \bif{\nleq(a,b)}{\nplus(c,a)}{\nplus(c,b)} \\
 & = & \nplus(c,\bif{\nleq(a,b)}{a}{b}) \\
 & = & \nplus(c,\nmin(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_max_next :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_max_next _ =
>   testName "max(next(a),next(b)) == next(max(a,b))" $
>   \a b -> eq (max (next a) (next b)) (next (max a b))
> 
> 
> _test_max_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_plus _ =
>   testName "max(plus(c,a),plus(c,b)) == plus(c,max(a,b))" $
>   \a b c -> eq (max (plus c a) (plus c b)) (plus c (max a b))
> 
> 
> _test_min_next :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_min_next _ =
>   testName "min(next(a),next(b)) == next(min(a,b))" $
>   \a b -> eq (min (next a) (next b)) (next (min a b))
> 
> 
> _test_min_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_plus _ =
>   testName "min(plus(c,a),plus(c,b)) == plus(c,min(a,b))" $
>   \a b c -> eq (min (plus c a) (plus c b)) (plus c (min a b))

</p></div>
</div>

$\ntimes$ distributes over $\nmax$ and $\nmin$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmax(\ntimes(c,a),\ntimes(c,b)) = \ntimes(c,\nmax(a,b))$.
2. $\nmin(\ntimes(c,a),\ntimes(c,b)) = \ntimes(c,\nmin(a,b))$.
</div>

<div class="proof"><p>
1. We consider two possibilities. If $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \nmax(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \nmax(\ntimes(\zero,a),\ntimes(\zero,b)) \\
 & = & \nmax(\zero,\zero) \\
 & = & \zero \\
 & = & \ntimes(\zero,\nmax(a,b)) \\
 & = & \ntimes(c,\nmax(a,b))
\end{eqnarray*}$$
as claimed. If $c = \next(d)$, we have
$$\begin{eqnarray*}
 &   & \nmax(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \bif{\nleq(\ntimes(c,a),\ntimes(c,b))}{\ntimes(c,b)}{\ntimes(c,a)} \\
 & = & \bif{\nleq(\ntimes(\next(d),a),\ntimes(\next(d),b))}{\ntimes(c,b)}{\ntimes(c,a)} \\
 & = & \bif{\nleq(a,b)}{\ntimes(c,b)}{\ntimes(c,a)} \\
 & = & \ntimes(c,\bif{\nleq(a,b)}{b}{a}) \\
 & = & \ntimes(c,\nmax(a,b))
\end{eqnarray*}$$
as claimed.
2. We consider two possibilities. If $c = \zero$, we have
$$\begin{eqnarray*}
 &   & \nmin(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \nmin(\ntimes(\zero,a),\ntimes(\zero,b)) \\
 & = & \nmin(\zero,\zero) \\
 & = & \zero \\
 & = & \ntimes(\zero,\nmin(a,b)) \\
 & = & \ntimes(c,\nmin(a,b))
\end{eqnarray*}$$
as claimed. If $c = \next(d)$, we have
$$\begin{eqnarray*}
 &   & \nmin(\ntimes(c,a),\ntimes(c,b)) \\
 & = & \bif{\nleq(\ntimes(c,a),\ntimes(c,b))}{\ntimes(c,a)}{\ntimes(c,b)} \\
 & = & \bif{\nleq(\ntimes(\next(d),a),\ntimes(\next(d),b))}{\ntimes(c,a)}{\ntimes(c,b)} \\
 & = & \bif{\nleq(a,b)}{\ntimes(c,b)}{\ntimes(c,a)} \\
 & = & \ntimes(c,\bif{\nleq(a,b)}{b}{a}) \\
 & = & \ntimes(c,\nmin(a,b))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_max_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_times _ =
>   testName "max(times(c,a),times(c,b)) == times(c,max(a,b))" $
>   \a b c -> eq (max (times c a) (times c b)) (times c (max a b))
> 
> 
> _test_min_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_times _ =
>   testName "min(times(c,a),times(c,b)) == times(c,min(a,b))" $
>   \a b c -> eq (min (times c a) (times c b)) (times c (min a b))

</p></div>
</div>

$\nmax$ and $\nmin$ are associative.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmax(a,\nmax(b,c)) = \nmax(\nmax(a,b),c)$.
2. $\nmin(a,\nmin(b,c)) = \nmin(\nmin(a,b),c)$.
</div>

<div class="proof"><p>
1. Set
$$\begin{eqnarray*}
 &   & \nmax(a,\nmax(b,c)) \\
 & = & \bif{\nleq(a,\nmax(b,c))}{\nmax(b,c)}{a} \\
 & = & \bif{\nleq(a,\bif{\nleq(b,c)}{c}{b})}{\nmax(b,c)}{a} \\
 & = & \bif{\bif{\nleq(b,c)}{\nleq(a,c)}{\nleq(a,b)}}{\nmax(b,c)}{a} \\
 & = & \bif{\bif{\nleq(b,c)}{\nleq(a,c)}{\nleq(a,b)}}{\bif{\nleq(b,c)}{c}{b}}{a} \\
 & = & Q
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \nmax(\nmax(a,b),c) \\
 & = & \bif{\nleq(\nmax(a,b),c)}{c}{\nmax(a,b)} \\
 & = & \bif{\nleq(\bif{\nleq(a,b)}{b}{a},c)}{c}{\nmax(a,b)} \\
 & = & \bif{\bif{\nleq(a,b)}{\nleq(b,c)}{\nleq(a,c)}}{c}{\nmax(a,b)} \\
 & = & \bif{\bif{\nleq(a,b)}{\nleq(b,c)}{\nleq(a,c)}}{c}{\bif{\nleq(a,b)}{b}{a}} \\
 & = & R.
\end{eqnarray*}$$
as claimed. If $\nleq(a,b) = \btrue$ and $\nleq(b,c) = \btrue$, by transitivity we have $\nleq(a,c) = \btrue$ and $$Q = \bif{\nleq(a,c)}{c}{a} = c = \bif{\nleq(b,c)}{c}{b} = R.$$ If $\nleq(a,b) = \btrue$ and $\nleq(b,c) = \bfalse$, we have $$Q = \bif{\nleq(a,b)}{b}{a} = b = \bif{\nleq(b,c)}{c}{b} = R.$$
Suppose $\nleq(a,b) = \bfalse$; then $\nleq(b,a) = \btrue$. If $\nleq(a,c) = \btrue$, we have $\nleq(b,c) = \btrue$ and $$Q = \bif{\nleq(a,c)}{c}{a} = R,$$ and if $\nleq(a,c) = \bfalse$, then $\nleq(c,a) = \btrue$ and $$Q = \bif{\bfalse}{\bif{\nleq(b,c)}{c}{b}}{a} = a = \bif{\nleq(a,c)}{c}{a} = R.$$
2. Analogous to (1).
</p></div>

<div class="test"><p>

> _test_max_associative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_associative _ =
>   testName "max(max(a,b),c) == max(a,max(b,c))" $
>   \a b c -> eq (max (max a b) c) (max a (max b c))
> 
> 
> _test_min_associative :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_associative _ =
>   testName "min(min(a,b),c) == min(a,min(b,c))" $
>   \a b c -> eq (min (min a b) c) (min a (min b c))

</p></div>
</div>

$\nmax$ and $\nmin$ satisfy a "least upper bound" and "greatest lower bound" property, respectively, with respect to $\nleq$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. If $\nleq(a,c)$ and $\nleq(b,c)$, then $\nleq(\nmax(a,b),c)$.
2. If $\nleq(c,a)$ and $\nleq(c,b)$, then $\nleq(c,\nmin(a,b))$.
3. $\nleq(\nmin(a,b),\nmax(a,b)) = \btrue$.
</div>

<div class="proof"><p>
1. If $\nleq(a,b) = \btrue$, then $\nmax(a,b) = b$, and if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, so that $\nmax(a,b) = a$. In either case we have $\nleq(\nmax(a,b),c)$.
2. If $\nleq(a,b) = \btrue$, then $\nmin(a,b) = a$, and if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, so that $\nmin(a,b) = b$. In either case we have $\nleq(c,\nmin(a,b))$.
3. Suppose $\nleq(a,b)$. Now $\nmin(a,b) = a$ and $\nmax(a,b) = b$, so that $$\nleq(\nmin(a,b),\nmax(a,b)) = \nleq(a,b) = \btrue$$ as claimed. Now if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, and we instead have $\nmin(a,b) = b$ and $\nmax(a,b) = a$.
</p></div>

<div class="test"><p>

> _test_max_lub :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_lub _ =
>   testName "if leq(a,c) and leq(b,c) then leq(max(a,b),c)" $
>   \a b c -> if and (leq a c) (leq b c)
>     then leq (max a b) c
>     else true
> 
> 
> _test_min_glb :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_glb _ =
>   testName "if leq(c,a) and leq(c,b) then leq(c,min(a,b))" $
>   \a b c -> if and (leq c a) (leq c b)
>     then leq c (min a b)
>     else true
> 
> 
> _test_max_min_leq :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_max_min_leq _ =
>   testName "leq(min(a,b),max(a,b))" $
>   \a b -> leq (min a b) (max a b)

</p></div>
</div>

$\nmax$ and $\nmin$ interact with $\nplus$ and $\ntimes$.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nplus(\nmin(a,b),\nmax(a,b)) = \nplus(a,b)$.
2. $\ntimes(\nmin(a,b),\nmax(a,b)) = \ntimes(a,b)$.
</div>

<div class="proof"><p>
We'll prove both of these at once. Suppose $\nleq(a,b)$. Now $\nmin(a,b) = a$ and $\nmax(a,b) = b$, so that $$\nplus(\nmin(a,b),\nmax(a,b)) = \nplus(a,b)$$ and $$\ntimes(\nmin(a,b),\nmax(a,b)) = \ntimes(a,b)$$ as claimed. Now if $\nleq(a,b) = \bfalse$, then $\nleq(b,a) = \btrue$, and we instead have $\nmin(a,b) = b$ and $\nmax(a,b) = a$. Then $$\nplus(\nmin(a,b),\nmax(a,b)) = \nplus(b,a) = \nplus(a,b)$$ and $$\ntimes(\nmin(a,b),\nmax(a,b)) = \ntimes(b,a) = \ntimes(a,b)$$ as claimed.
</p></div>

<div class="test"><p>

> _test_max_min_plus :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_max_min_plus _ =
>   testName "plus(min(a,b),max(a,b)) == plus(a,b)" $
>   \a b -> eq (plus (min a b) (max a b)) (plus a b)
> 
> 
> _test_max_min_times :: (Natural n, Equal n)
>   => n -> Test (n -> n -> Bool)
> _test_max_min_times _ =
>   testName "times(min(a,b),max(a,b)) == times(a,b)" $
>   \a b -> eq (times (min a b) (max a b)) (times a b)

</p></div>
</div>

And $\nmax$ and $\nmin$ distribute over each other.

<div class="result">
<div class="thm">
Let $a,b,c \in \nats$. Then we have the following.

1. $\nmin(a,\nmax(b,c)) = \nmax(\nmin(a,b),\nmin(a,c))$.
2. $\nmax(a,\nmin(b,c)) = \nmin(\nmax(a,b),\nmax(a,c))$.
3. $\nmin(\nmax(b,c),a) = \nmax(\nmin(b,a),\nmin(c,a))$.
4. $\nmax(\nmin(b,c),a) = \nmin(\nmax(b,a),\nmax(c,a))$.
</div>

<div class="proof"><p>
4. Brute force time! Suppose $\nleq(a,b) = \btrue$. If $\nleq(a,c) = \btrue$, then $\nleq(a,\nmin(b,c))$, so that $\nleq(a,\nmax(b,c))$. Now we have $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(a,a) \\ & = & a \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ Suppose $\nleq(a,c) = \bfalse$; then $\nleq(c,a) = \btrue$, and by transitivity $\nleq(c,b) = \btrue$ so that $\nmax(b,c) = b$. Now $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(a,c) \\ & = & a \\ & = & \nmin(a,b) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ Now suppose $\nleq(a,b) = \bfalse$, so that $\nleq(b,a) = \btrue$. If $\nleq(a,c)$, then $\nleq(b,c)$ by transitivity. So we have $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(b,a) \\ & = & a \\ & = & \nmin(a,c) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$ If $\nleq(a,c) = \bfalse$, then $\nleq(c,a) = \btrue$. In this case we have $\nleq(\nmax(b,c),a)$, so that $$\begin{eqnarray*} & & \nmax(\nmin(a,b),\nmin(a,c)) \\ & = & \nmax(b,c) \\ & = & \nmin(a,\nmax(b,c)). \end{eqnarray*}$$
5. Similar to (4), which we can agree was super tedious.
6. Follows from (4) and commutativity.
7. Follows from (5) and commutativity.
</p></div>

<div class="test"><p>

> _test_max_min_distributive_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_min_distributive_left _ =
>   testName "max(a,min(b,c)) == min(max(a,b),max(a,c))" $
>   \a b c -> eq (max a (min b c)) (min (max a b) (max a c))
> 
> 
> _test_max_min_distributive_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_max_min_distributive_right _ =
>   testName "max(min(b,c),a) == min(max(b,a),max(c,a))" $
>   \a b c -> eq (max (min b c) a) (min (max b a) (max c a))
> 
> 
> _test_min_max_distributive_left :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_max_distributive_left _ =
>   testName "min(a,max(b,c)) == max(min(a,b),min(a,c))" $
>   \a b c -> eq (min a (max b c)) (max (min a b) (min a c))
> 
> 
> _test_min_max_distributive_right :: (Natural n, Equal n)
>   => n -> Test (n -> n -> n -> Bool)
> _test_min_max_distributive_right _ =
>   testName "min(max(b,c),a) == max(min(b,a),min(c,a))" $
>   \a b c -> eq (min (max b c) a) (max (min b a) (min c a))

</p></div>
</div>

woo!


Testing
-------

Suite:

> -- run all tests for max and min
> _test_max_min ::
>   ( TypeName n, Natural n, Equal n, Arbitrary n, Show n
>   ) => n -> Int -> Int -> IO ()
> _test_max_min n maxSize numCases = do
>   testLabel1 "min & max" n
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_max_zero n)
>   runTest args (_test_max_idempotent n)
>   runTest args (_test_min_zero n)
>   runTest args (_test_min_idempotent n)
>   runTest args (_test_max_commutative n)
>   runTest args (_test_min_commutative n)
>   runTest args (_test_max_next n)
>   runTest args (_test_max_plus n)
>   runTest args (_test_min_next n)
>   runTest args (_test_min_plus n)
>   runTest args (_test_max_times n)
>   runTest args (_test_min_times n)
>   runTest args (_test_max_associative n)
>   runTest args (_test_min_associative n)
>   runTest args (_test_max_lub n)
>   runTest args (_test_min_glb n)
>   runTest args (_test_max_min_leq n)
>   runTest args (_test_max_min_plus n)
>   runTest args (_test_max_min_times n)
>   runTest args (_test_max_min_distributive_left n)
>   runTest args (_test_max_min_distributive_right n)
>   runTest args (_test_min_max_distributive_left n)
>   runTest args (_test_min_max_distributive_right n)

Main:

> main_max_min :: IO ()
> main_max_min = do
>   _test_max_min (zero :: Unary) 100 100
