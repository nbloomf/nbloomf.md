---
title: Prefix
author: nbloomf
date: 2017-05-08
tags: arithmetic-made-difficult, literate-haskell
---

> module Prefix
>   ( prefix, suffix, _test_prefix, main_prefix
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import Lists
> import Reverse
> import Cat
> import Zip
> 
> import Prelude ()
> import Test.QuickCheck

The $\cat$ function on $\lists{A}$ is analogous to $\nplus$ on $\nats$. Carrying this analogy further, $\zip$ and $\zipPad$ are analogous to $\nmin$ and $\nmax$, respectively. When analogies like this occur in mathematics it can be fruitful to see how far they go. With that in mind, today we will explore the list-analogue of $\nleq$. This role is played by two functions which we call $\prefix$ and $\suffix$.

Intuitively, $\prefix$ will detect when one list is an initial segment of another, while $\suffix$ detects when one list is a terminal segment of another. We'll start with $\prefix$. This function should have a signature like $$\lists{A} \times \lists{A} \rightarrow \bool.$$ But how to define this as a fold? Taking a cue from our definition of $\zip$, we'll look for $\varepsilon$ and $\varphi$ so that $$\prefix(x,y) = \foldr{\varepsilon}{\varphi}(x)(y)$$ behaves as expected. So we want $$\varepsilon : \bool^{\lists{A}}$$ such that
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y).
\end{eqnarray*}$$
Similarly, we want $$\varphi : A \times \bool^{\lists{A}} \rightarrow \bool^{\lists{A}}$$ such that
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \prefix(\cons(a,x),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\nil),
\end{eqnarray*}$$
while if $a = b$, we want
$$\begin{eqnarray*}
 &   & \prefix(x,y) \\
 & = & \prefix(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
\end{eqnarray*}$$
and if $a \neq b$, we want
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \prefix(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)). \\
\end{eqnarray*}$$

So motivated, we define $\prefix$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \bool$ by $$\varepsilon(y) = \btrue.$$ Define $\varphi : A \times \bool^{\lists{A}} \rightarrow \bool^{\lists{A}}$ by $$\varphi(a,f)(w) = \left\{\begin{array}{ll} f(u) & \mathrm{if}\ w = \cons(b,u)\ \mathrm{and}\ a = b \\ \bfalse & \mathrm{otherwise.} \end{array}\right.$$ Then we define $$\prefix : \lists{A} \times \lists{A} \rightarrow \bool$$ by $$\prefix(x,y) = \foldr{\varepsilon}{\varphi}(x)(y).$$
</p></div>
</div>

We can translate this definition directly to Haskell:

> prefix' :: (List t, Equal a) => t a -> t a -> Bool
> prefix' = foldr epsilon phi
>   where
>     epsilon _ = True
> 
>     phi a f w = case listShape w of
>       Nil      -> False
>       Cons b u -> if a ==== b
>         then f u
>         else False

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$, we have the following.

1. $\prefix(\nil,y) = \btrue$.
2. $\prefix(\cons(a,x),\nil) = \bfalse$.
3. $$\prefix(\cons(a,x),\cons(b,y)) = \left\{\begin{array}{ll} \bfalse & \mathrm{if}\ a \neq b \\ \prefix(x,y) & \mathrm{if}\ a = b. \end{array}\right.$$
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \prefix(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,x),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. First suppose $a = b$. Now
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(x)(y) \\
 & = & \prefix(x,y)
\end{eqnarray*}$$
as claimed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> prefix :: (List t, Equal a) => t a -> t a -> Bool
> prefix u v = case listShape u of
>   Nil      -> True
>   Cons a x -> case listShape v of
>     Nil      -> False
>     Cons b y -> if a ==== b
>       then prefix x y
>       else False

Now $\prefix$ is analogous to $\nleq$ in that it detects the existence of solutions $z$ to the equation $y = \cat(x,z)$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y \in \lists{A}$.

1. $\prefix(x,\cat(x,y)) = \btrue$.
2. If $\prefix(x,y) = \btrue$, then $y = \cat(x,z)$ for some $z \in \lists{A}$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, certainly we have
$$\begin{eqnarray*}
 &   & \prefix(x,\cat(x,y)) \\
 & = & \prefix(\nil,\cat(\nil,y)) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue.
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $x$, and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,x),\cat(\cons(a,x),y)) \\
 & = & \prefix(\cons(a,x),\cons(a,\cat(x,y))) \\
 & = & \prefix(x,\cat(x,y)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that $$\prefix(\nil,y) = \btrue,$$ and $$y = \cat(\nil,y).$$ For the inductive step, suppose the result holds for some $x$, and let $a \in A$. Now suppose $\prefix(\cons(a,x),y) = \btrue$; in particular, we must have $y = \cons(a,w)$ for some $w$, and $\prefix(x,w) = \btrue$. By the induction hypothesis we have $w = \cat(x,z)$ for some $z$, and thus
$$\begin{eqnarray*}
 &   & y \\
 & = & \cons(a,w) \\
 & = & \cons(a,\cat(x,z)) \\
 & = & \cat(\cons(a,x),z)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\prefix$ is a partial order:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Then we have the following for all $x,y,z \in \lists{A}$.

1. $\prefix(x,x) = \btrue$.
2. If $\prefix(x,y)$ and $\prefix(y,x)$, then $x = y$.
3. If $\prefix(x,y)$ and $\prefix(y,z)$, then $\prefix(x,z)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(x,\cat(x,\nil)) \\
 & = & \prefix(x,x)
\end{eqnarray*}$$
as claimed.
2. If $\prefix(x,y)$, we have $y = \cat(x,u)$ for some $u$. Similarly, if $\prefix(y,x)$ then $x = \cat(y,v)$ for some $v. Now
$$\begin{eqnarray*}
 &   & \cat(x,\nil) \\
 & = & x \\
 & = & \cat(y,v) \\
 & = & \cat(\cat(x,u),v) \\
 & = & \cat(x,\cat(u,v)).
\end{eqnarray*}$$
Since $\cat$ is cancellative, we have $\nil = \cat(u,v)$, so that $u = \nil$, and thus $x = y$ as claimed.
3. If $\prefix(x,y)$, we have $y = \cat(x,u)$. Similarly, if $\prefix(y,z)$, we have $z = \cat(y,v)$. Now $$z = \cat(\cat(x,u),v) = \cat(x,\cat(u,v))$$ so that $\prefix(x,z)$ as claimed.
</p></div>
</div>

$\map$ preserves prefixes:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$, and let $x,y \in \lists{A}$. If $\prefix(x,y) = \btrue$, then $$\prefix(\map(f)(x),\map(f)(y)) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,y) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\map(f)(x),\map(f)(y)) \\
 & = & \prefix(\map(f)(\nil),\map(f)(y)) \\
 & = & \prefix(\nil,\map(f)(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose now the implication holds for some $x$, and let $a \in A$. Suppose further that $\prefix(\cons(a,x),y)$. Now $y = \cons(a,w)$ for some $w$, and we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\cons(a,x),y) \\
 & = & \prefix(\cons(a,x),\cons(a,w)) \\
 & = & \prefix(x,w).
\end{eqnarray*}$$
Using the induction hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\map(f)(\cons(a,x)),\map(f)(y)) \\
 & = & \prefix(\map(f)(\cons(a,x)),\map(f)(\cons(a,w))) \\
 & = & \prefix(\cons(f(a),\map(f)(x)),\cons(f(a),\map(f)(w))) \\
 & = & \prefix(\map(f)(x),\map(f)(w)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\zip$ preserves prefixes.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $x,y \in \lists{A}$ and $u,v \in \lists{B}$. If $\prefix(x,y) = \btrue$ and $\prefix(u,v) = \btrue$, then $$\prefix(\zip(x,u),\zip(y,v)) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that $\prefix(x,y) = \btrue$. Suppose further that $\prefix(u,v) = \btrue$; now
$$\begin{eqnarray*}
 &   & \prefix(\zip(x,u),\zip(y,v)) \\
 & = & \prefix(\zip(\nil,u),\zip(y,v)) \\
 & = & \prefix(\nil,\zip(y,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the implication holds for some $x$ and let $a \in A$. Suppose further that $\prefix(\cons(a,x),y)$ and $\prefix(u,v)$; in particular we must have $y = \cons(a,k)$ for some $k \in \lists{A}$ with $\prefix(x,k)$, as otherwise $\prefix(\cons(a,x),y) = \bfalse$. Now we have two possibilities for $u$. If $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \prefix(\zip(\cons(a,x),\nil),\zip(y,v)) \\
 & = & \prefix(\nil,\zip(y,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose then that $u = \cons(b,w)$. Again we must have $v = \cons(b,h)$ with $h \in \lists{B}$ and $\prefix(w,h)$, since otherwise we have $\prefix(u,v) = \bfalse$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \prefix(\zip(\cons(a,x),\cons(b,w)),\zip(\cons(a,k),\cons(b,h))) \\
 & = & \prefix(\cons((a,b),\zip(x,w)),\cons((a,b),\zip(k,h))) \\
 & = & \prefix(\zip(x,w),\zip(k,h)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

The simplest way to define $\suffix$ is in terms of $\prefix$.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\suffix : \lists{A} \times \lists{A} \rightarrow \bool$ by $$\suffix(x,y) = \prefix(\rev(x),\rev(y)).$$

In Haskell:

> suffix :: (List t, Equal a) => t a -> t a -> Bool
> suffix x y = prefix (rev x) (rev y)

</p></div>
</div>

Not surprisingly, we can characterize $\prefix$ in terms of $\suffix$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. Then $$\prefix(x,y) = \suffix(\rev(x),\rev(y)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \suffix(\rev(x),\rev(y)) \\
 & = & \prefix(\rev(\rev(x)),\rev(\rev(y))) \\
 & = & \prefix(x,y)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Many theorems about $\prefix$ has an analogue for $\suffix$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a,b \in A$ and $x,y \in \lists{A}$, we have the following.

1. $\suffix(\nil,y) = \btrue$.
2. $\suffix(\snoc(a,x),\nil) = \bfalse$.
3. $$\suffix(\snoc(a,x),\snoc(b,y)) = \left\{\begin{array}{ll} \bfalse & \mathrm{if}\ a \neq b \\ \suffix(x,y) & \mathrm{if}\ a = b. \end{array}\right.$$
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \suffix(\nil,y) \\
 & = & \prefix(\rev(\nil),\rev(y)) \\
 & = & \prefix(\nil,\rev(y)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\nil) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\nil)) \\
 & = & \prefix(\cons(a,\rev(x)),\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. First suppose $a = b$. Now
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\snoc(b,y)) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\snoc(b,y))) \\
 & = & \prefix(\cons(a,\rev(x)),\cons(b,\rev(y))) \\
 & = & \prefix(\rev(x),\rev(y)) \\
 & = & \suffix(x,y)
\end{eqnarray*}$$
as claimed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \suffix(\snoc(a,x),\snoc(b,y)) \\
 & = & \prefix(\rev(\snoc(a,x)),\rev(\snoc(b,y))) \\
 & = & \prefix(\cons(a,\rev(x)),\cons(b,\rev(y))) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Like $\prefix$, $\suffix$ also detects the existence of solutions $z$ to the equation $y = \cat(z,x)$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y \in \lists{A}$.

1. $\suffix(x,\cat(y,x)) = \btrue$.
2. If $\suffix(x,y) = \btrue$, then $y = \cat(z,x)$ for some $z \in \lists{A}$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \suffix(x,\cat(y,x)) \\
 & = & \prefix(\rev(x),\rev(\cat(y,x))) \\
 & = & \prefix(\rev(x),\cat(\rev(x),\rev(y))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Suppose $\suffix(x,y) = \btrue$. Then $\prefix(\rev(x),\rev(y)) = \btrue$, so we have $\rev(y) = \cat(\rev(x),w)$ for some $w$. Now
$$\begin{eqnarray*}
 &   & y \\
 & = & \rev(\rev(y)) \\
 & = & \rev(\cat(\rev(x),w)) \\
 & = & \cat(\rev(w),\rev(\rev(x))) \\
 & = & \cat(\rev(w),x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\suffix$ is a partial order:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. Then we have the following for all $x,y,z \in \lists{A}$.

1. $\suffix(x,x) = \btrue$.
2. If $\suffix(x,y)$ and $\suffix(y,x)$, then $x = y$.
3. If $\suffix(x,y)$ and $\suffix(y,z)$, then $\suffix(x,z)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\rev(x),\rev(x)) \\
 & = & \suffix(x,x)
\end{eqnarray*}$$
as claimed.
2. If $\suffix(x,y)$, we have $y = \cat(u,x)$ for some $u$. Similarly, if $\suffix(y,x)$ then $x = \cat(v,y)$ for some $v$. Now
$$\begin{eqnarray*}
 &   & \cat(\nil,x) \\
 & = & x \\
 & = & \cat(v,y) \\
 & = & \cat(v,\cat(u,x)) \\
 & = & \cat(\cat(v,u),x).
\end{eqnarray*}$$
Since $\cat$ is cancellative, we have $\nil = \cat(v,u)$, so that $u = \nil$, and thus $x = y$ as claimed.
3. If $\suffix(x,y)$ and $\suffix(y,z)$, then $\prefix(\rev(x),\rev(y))$ and $\prefix(\rev(y),\rev(z))$. So $\prefix(\rev(x),\rev(z))$, and thus $\suffix(x,z)$.
</p></div>
</div>

$\map$ preserves suffixes:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$, and let $x,y \in \lists{A}$. If $\suffix(x,y) = \btrue$, then $$\suffix(\map(f)(x),\map(f)(y)) = \btrue.$$
</p></div>

<div class="proof"><p>
Suppose $\suffix(x,y)$; then $\prefix(\rev(x),\rev(y))$. Then we have
$$\begin{eqnarray*}
 &   & \suffix(\map(f)(x),\map(f)(y)) \\
 & = & \prefix(\rev(\map(f)(x)),\rev(\map(f)(y))) \\
 & = & \prefix(\map(f)(\rev(x)),\map(f)(\rev(y))) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Finally:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. If $y \neq \cons(a,x)$, then $$\suffix(y,x) = \suffix(y,\cons(a,x)).$$
</p></div>

<div class="proof"><p>
Suppose $\suffix(y,x) = \btrue$. Then we have $x = \cat(z,y)$, so that $$\cons(a,x) = \cons(a,\cat(z,y)) = \cat(\cons(a,z),y),$$ so that $\suffix(y,\cons(a,x))$.

Conversely, suppose $\suffix(y,\cons(a,x)) = \btrue$. Then we have $\cons(a,x) = \cat(z,y)$ for some $z$. If $z = \nil$, then $\cons(a,x) = y$; a contradiction. Say then that $z = \cons(b,w)$. Now
$$\begin{eqnarray*}
 &   & \cons(a,x) \\
 & = & \cat(z,y) \\
 & = & \cat(\cons(b,w),y) \\
 & = & \cons(b,\cat(w,y));
</p></div>
in particular we must have $a = b$ and $x = \cat(w,y)$. Thus $\suffix(y,x) = \btrue$.
</div>


Testing
-------

Here are our property tests for $\prefix$ and $\suffix$.

> -- prefix(x,cat(x,y))
> _test_prefix_cat :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_prefix_cat _ x y =
>   prefix x (cat x y)
> 
> 
> -- prefix(x,x)
> _test_prefix_reflexive :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_prefix_reflexive _ x =
>   prefix x x
> 
> 
> -- prefix(x,y) & prefix(y,z) ==> prefix(x,z)
> _test_prefix_transitive :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_prefix_transitive _ x y z =
>   if (prefix x y) &&& (prefix y z)
>     then prefix x z
>     else True
> 
> 
> -- prefix(x,y) & prefix(u,v) ==> prefix(zip(x,u),zip(y,v))
> _test_prefix_zip :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_prefix_zip _ x y u v =
>   if (prefix x y) &&& (prefix u v)
>     then prefix (zip x u) (zip y v)
>     else True

Tests for $\suffix$:

> -- suffix(y,cat(x,y))
> _test_suffix_cat :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_suffix_cat _ x y =
>   suffix y (cat x y)
> 
> 
> -- suffix(x,x)
> _test_suffix_reflexive :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_suffix_reflexive _ x =
>   suffix x x
> 
> 
> -- suffix(x,y) & suffix(y,z) ==> suffix(x,z)
> _test_suffix_transitive :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> ListOf t a -> Bool
> _test_suffix_transitive _ x y z =
>   if (suffix x y) &&& (suffix y z)
>     then suffix x z
>     else True

And the suite:

> -- run all tests for prefix & suffix
> _test_prefix ::
>   ( TypeName a, Show a, Equal a, Arbitrary a
>   , TypeName (t a), List t
>   ) => t a -> Int -> Int -> IO ()
> _test_prefix t maxSize numCases = do
>   testLabel ("prefix & suffix: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_prefix_cat t)
>   runTest args (_test_prefix_reflexive t)
>   runTest args (_test_prefix_transitive t)
>   runTest args (_test_prefix_zip t)
> 
>   runTest args (_test_suffix_cat t)
>   runTest args (_test_suffix_reflexive t)
>   runTest args (_test_suffix_transitive t)

And ``main``:

> main_prefix :: IO ()
> main_prefix = do
>   _test_prefix (nil :: ConsList Bool)  20 100
>   _test_prefix (nil :: ConsList Unary) 20 100
