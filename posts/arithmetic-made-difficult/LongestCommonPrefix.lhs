---
title: Longest Common Prefix
author: nbloomf
date: 2017-05-09
tags: arithmetic-made-difficult, literate-haskell
---

> module LongestCommonPrefix
>   ( lcp, lcs, _test_lcp, main_lcp
>   ) where
> 
> import Prelude hiding (foldr, foldl', foldl, map, zip)
> 
> import Lists
> import Reverse
> import Cat
> import Zip
> import Prefix
> 
> import Test.QuickCheck

Today we'll compute the *longest common prefix* of two strings (and while we're at it, the *longest common suffix*). Given two lists $x$ and $y$, their longest common prefix is the longest list which is a prefix of both, just like it says on the tin. We'll denote this function $\lcp$, and we want it to have a signature like $$\lists{A} \times \lists{A} \rightarrow \lists{A}.$$ To define $\lcp$ as a fold like $$\lcp(x,y) = \foldr{\varepsilon}{\varphi}(x)(y)$$ we need $\varepsilon : \lists{A}^{\lists{A}}$ such that
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \lcp(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y),
\end{eqnarray*}$$
and $$\varphi : A \times \lists{A}^{\lists{A}} \rightarrow \lists{A}^{\lists{A}}$$ such that
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \lcp(\cons(a,x),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\nil)
\end{eqnarray*}$$
and if $a = b$, then
$$\begin{eqnarray*}
 &   & \cons(a,\lcp(x,y)) \\
 & = & \lcp(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
\end{eqnarray*}$$
while if $a \neq b$, we want
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \lcp(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y))
\end{eqnarray*}$$
With this in mind, we define $\lcp$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \lists{A}$ by $$\varepsilon(y) = \nil$$ and define $\varphi : A \times \lists{A}^{\lists{A}} \rightarrow \lists{A}^{\lists{A}}$ by $$\varphi(a,f)(w) = \left\{ \begin{array}{ll} \cons(a,f(u)) & \mathrm{if}\ w = \cons(a,u) \\ \nil & \mathrm{otherwise}. \end{array} \right.$$ Now define $\lcp : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\lcp(x,y) = \foldr{\varepsilon}{\varphi}(x)(y).$$
</p></div>
</div>

We can translate $\lcp$ to Haskell directly as follows:

> lcp' :: (ListOf t, Eq a) => t a -> t a -> t a
> lcp' = foldr epsilon phi
>   where
>     epsilon _ = nil
> 
>     phi a f w = case listShape w of
>       Nil      -> nil
>       Cons b u -> if a == b
>         then cons a (f u)
>         else nil

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$ and $a,b \in A$. Then we have the following.

1. $\lcp(\nil,y) = \nil$.
2. $\lcp(x,\nil) = \nil$.
3. $$\lcp(\cons(a,x),\cons(b,y)) = \left\{ \begin{array}{ll} \cons(a,\lcp(x,y)) & \mathrm{if} a = b \\ \nil & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
3. (@@@)
</p></div>
</div>

In Haskell:

> lcp :: (ListOf t, Eq a) => t a -> t a -> t a
> lcp x y = case listShape x of
>   Nil      -> nil
>   Cons a u -> case listShape y of
>     Nil      -> nil
>     Cons b v -> if a == b
>       then cons a (lcp u v)
>       else nil

Now $\lcp$ lives up to the name (the *universal property* of $\lcp$):

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,z \in \lists{A}$.

1. $\prefix(\lcp(x,y),x)$ and $\prefix(\lcp(x,y),y)$.
2. If $\prefix(z,x)$ and $\prefix(z,y)$, then $\prefix(z,\lcp(x,y))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(x,y),x) \\
 & = & \prefix(\lcp(\nil,y),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(x,y),y) \\
 & = & \prefix(\lcp(\nil,y),y) \\
 & = & \prefix(\nil,y) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equalities hold for all $y$ for some $x$, and let $a \in A$. We consider two cases for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\nil),\cons(a,x)) \\
 & = & \prefix(\nil,\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose now that $y = \cons(b,w)$. If $b = a$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(a,w)),\cons(a,x)) \\
 & = & \prefix(\cons(a,\lcp(x,w)),\cons(a,x)) \\
 & = & \prefix(\lcp(x,w),x) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(b,w)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(a,w)),\cons(a,w)) \\
 & = & \prefix(\cons(a,\lcp(x,w)),\cons(a,w)) \\
 & = & \prefix(\lcp(x,w),w) \\
 & = & \btrue,
\end{eqnarray*}$$
while if $b \neq a$, we have
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),\cons(a,x)) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(a,x)) \\
 & = & \prefix(\nil,\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \prefix(\lcp(\cons(a,x),y),y) \\
 & = & \prefix(\lcp(\cons(a,x),\cons(b,w)),\cons(b,w)) \\
 & = & \prefix(\nil,\cons(b,w)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
2. (@@@)
</p></div>
</div>

$\lcp$ satisfies some nice identities:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,z \in \lists{A}$.

1. $\lcp(x,x) = x$.
2. $\lcp(x,y) = \lcp(y,x)$.
3. $\lcp(\lcp(x,y),z) = \lcp(x,\lcp(y,z))$.
4. $\cat(x,\lcp(y,z)) = \lcp(\cat(x,y),\cat(x,z))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(x,x) \\
 & = & \lcp(\nil,\nil) \\
 & = & \nil \\
 & = & x
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),\cons(a,x)) \\
 & = & \cons(a,\lcp(x,x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(x,y) \\
 & = & \lcp(\nil,y) \\
 & = & \nil \\
 & = & \lcp(y,\nil) \\
 & = & \lcp(y,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$, and let $a \in A$. Now we consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),y) \\
 & = & \lcp(\cons(a,x),\nil) \\
 & = & \nil \\
 & = & \lcp(\nil,\cons(a,x)) \\
 & = & \lcp(y,\cons(a,x))
\end{eqnarray*}$$
as needed. Now suppose $y = \cons(b,w)$. If $b \neq a$, we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),y) \\
 & = & \lcp(\cons(a,x),\cons(b,w)) \\
 & = & \nil \\
 & = & \lcp(\cons(b,w),\cons(a,x)) \\
 & = & \lcp(y,\cons(a,x)),
\end{eqnarray*}$$
while if $a = b$, we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),y) \\
 & = & \lcp(\cons(a,x),\cons(b,w)) \\
 & = & \lcp(\cons(a,x),\cons(a,w)) \\
 & = & \cons(a,\lcp(x,w)) \\
 & = & \cons(a,\lcp(w,x)) \\
 & = & \lcp(\cons(a,w),\cons(a,x)) \\
 & = & \lcp(\cons(b,w),\cons(a,x)) \\
 & = & \lcp(y,\cons(a,x))
\end{eqnarray*}$$
as needed.
3. (@@@)
4. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \cat(x,\lcp(y,z)) \\
 & = & \cat(\nil,\lcp(y,z)) \\
 & = & \lcp(y,z) \\
 & = & \lcp(\cat(\nil,y),\cat(\nil,z)) \\
 & = & \lcp(\cat(x,y),\cat(x,z))
\end{eqnarray*}$$
as needed. Suppose now that the equality holds for all $y$ and $z$ for some $x$, and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \cat(\cons(a,x),\lcp(y,z)) \\
 & = & \cons(a,\cat(x,\lcp(y,z))) \\
 & = & \cons(a,\lcp(\cat(x,y),\cat(x,z))) \\
 & = & \lcp(\cons(a,\cat(x,y)),\cons(a,\cat(x,z))) \\
 & = & \lcp(\cat(\cons(a,x),y),\cat(\cons(a,x),z))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\lcp$ detects prefixes:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. Then $\lcp(x,y) = x$ if and only if $\prefix(x,y) = \btrue$.
</p></div>

<div class="proof"><p>
To see the "if" part, suppose $\prefix(x,y)$. Then we have $y = \cat(x,z)$ for some $z$. Now
$$\begin{eqnarray*}
 &   & \lcp(x,y) \\
 & = & \lcp(\cat(x,\nil),\cat(x,z)) \\
 & = & \cat(x,\lcp(\nil,z)) \\
 & = & \cat(x,\nil) \\
 & = & x
\end{eqnarray*}$$
as claimed.

To see the "only if" part, suppose we have $\lcp(x,y) = x$; using the universal property of $\lcp$, we have
$$\begin{eqnarray*}
 &   & \prefix(x,y) \\
 & = & \prefix(\lcp(x,y),y) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\lcp$ interacts with $\zip$.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $x,y \in \lists{A}$ and $u,v \in \lists{B}$. Then $$\lcp(\zip(x,u),\zip(y,v)) = \zip(\lcp(x,y),\lcp(u,v)).$$
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>

We can define the dual operation, longest common suffix, in terms of $\lcp$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\lcs : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\lcs(x,y) = \rev(\lcp(\rev(x),\rev(y))).$$

In Haskell:

> lcs :: (ListOf t, Eq a) => t a -> t a -> t a
> lcs x y = rev (lcp (rev x) (rev y))

</p></div>
</div>

$\lcs$ lives up to the name:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y,z \in \lists{A}$. Then we have the following.

1. $\suffix(\lcs(x,y),x)$ and $\suffix(\lcs(x,y),y)$.
2. If $\suffix(z,x)$ and $\suffix(z,y)$, then $\suffix(z,\lcs(x,y))$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
</p></div>
</div>

$\lcs$ satisfies some nice identities:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. The following hold for all $x,y,z \in \lists{A}$.

1. $\lcs(x,x) = x$.
2. $\lcs(x,y) = \lcs(y,x)$.
3. $\lcs(\lcs(x,y),z) = \lcs(x,\lcs(y,z))$.
4. $\cat(\lcs(x,y),z) = \lcs(\cat(x,z),\cat(y,z))$.
</p></div>

<div class="proof"><p>
1. (@@@)
2. (@@@)
3. (@@@)
4. (@@@)
</p></div>
</div>

And $\lcs$ detects suffixes:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. Then $\lcs(x,y) = x$ if and only if $\suffix(x,y)$.
</p></div>

<div class="proof"><p>
(@@@)
</p></div>
</div>


Testing
-------

Here are our property tests for $\lcp$ and $\lcs$.

> -- lcp(x,y) == lcp'(x,y)
> _test_lcp_alt :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_lcp_alt _ x y =
>   (lcp x y) `listEq` (lcp' x y)
> 
> 
> -- lcp(x,x) == x
> _test_lcp_idempotent :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_lcp_idempotent _ x =
>   (lcp x x) `listEq` x
> 
> 
> -- lcp(x,y) == lcp(y,x)
> _test_lcp_commutative :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_lcp_commutative _ x y =
>   (lcp x y) `listEq` (lcp y x)
> 
> 
> -- lcp(lcp(x,y),z) == lcp(x,lcp(y,z))
> _test_lcp_associative :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_lcp_associative _ x y z =
>   (lcp (lcp x y) z) `listEq` (lcp x (lcp y z))
> 
> 
> -- cat(x,lcp(y,z)) == lcp(cat(x,y),cat(x,z))
> _test_lcp_cat :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_lcp_cat _ x y z =
>   (cat x (lcp y z)) `listEq` (lcp (cat x y) (cat x z))
> 
> 
> -- lcp(x,y) == x iff prefix(x,y)
> _test_lcp_prefix :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_lcp_prefix _ x y =
>   ((lcp x y) `listEq` x) == (prefix x y)
> 
> 
> -- zip(lcp(x,y),lcp(u,v)) == lcp(zip(x,u),zip(y,v))
> _test_lcp_zip :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> t a -> Bool
> _test_lcp_zip _ x y u v =
>   (zip (lcp x y) (lcp u v)) `listEq` (lcp (zip x u) (zip y v))

Tests for $\lcs$:

> -- lcs(x,x) == x
> _test_lcs_idempotent :: (ListOf t, Eq a)
>   => t a -> t a -> Bool
> _test_lcs_idempotent _ x =
>   (lcs x x) `listEq` x
> 
> 
> -- lcs(x,y) == lcs(y,x)
> _test_lcs_commutative :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_lcs_commutative _ x y =
>   (lcs x y) `listEq` (lcs y x)
> 
> 
> -- lcs(lcs(x,y),z) == lcs(x,lcs(y,z))
> _test_lcs_associative :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_lcs_associative _ x y z =
>   (lcs (lcs x y) z) `listEq` (lcs x (lcs y z))
> 
> 
> -- cat(lcs(x,y),z) == lcs(cat(x,z),cat(y,z))
> _test_lcs_cat :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> t a -> Bool
> _test_lcs_cat _ x y z =
>   (cat (lcs x y) z) `listEq` (lcs (cat x z) (cat y z))
> 
> 
> -- lcs(x,y) == x iff suffix(x,y)
> _test_lcs_suffix :: (ListOf t, Eq a)
>   => t a -> t a -> t a -> Bool
> _test_lcs_suffix _ x y =
>   ((lcs x y) `listEq` x) == (suffix x y)

And the suite:

> -- run all tests for lcp and lcs
> _test_lcp :: (ListOf t, Arbitrary a, Show a, Eq a, Arbitrary (t a), Show (t a))
>   => t a -> Int -> Int -> IO ()
> _test_lcp t maxSize numCases = sequence_
>   [ quickCheckWith args (_test_lcp_alt t)
>   , quickCheckWith args (_test_lcp_idempotent t)
>   , quickCheckWith args (_test_lcp_commutative t)
>   , quickCheckWith args (_test_lcp_associative t)
>   , quickCheckWith args (_test_lcp_cat t)
>   , quickCheckWith args (_test_lcp_prefix t)
>   , quickCheckWith args (_test_lcp_zip t)
> 
>   , quickCheckWith args (_test_lcs_idempotent t)
>   , quickCheckWith args (_test_lcs_commutative t)
>   , quickCheckWith args (_test_lcs_associative t)
>   , quickCheckWith args (_test_lcs_cat t)
>   , quickCheckWith args (_test_lcs_suffix t)
>   ]
>   where
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }

And ``main``:

> main_lcp :: IO ()
> main_lcp = _test_lcp (nil :: List Bool) 20 100
