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
> import Booleans
> import NaturalNumbers
> import Lists
> import Reverse
> import Cat
> import Zip
> import Prefix
>
> import Prelude ()
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

> lcp' :: (List t, Equal a) => t a -> t a -> t a
> lcp' = foldr epsilon phi
>   where
>     epsilon _ = nil
> 
>     phi a f w = case uncons w of
>       Left ()     -> nil
>       Right (b,u) -> if eq a b
>         then cons a (f u)
>         else nil

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$ and $a,b \in A$. Then we have the following.

1. $\lcp(\nil,y) = \nil$.
2. $\lcp(x,\nil) = \nil$.
3. $$\lcp(\cons(a,x),\cons(b,y)) = \left\{ \begin{array}{ll} \cons(a,\lcp(x,y)) & \mathrm{if}\ a = b \\ \nil & \mathrm{otherwise}. \end{array} \right.$$
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \lcp(\nil,y) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(y) \\
 & = & \varepsilon(y) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\nil) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. If $a = b$ we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(a,y)) \\
 & = & \cons(a,\foldr{\varepsilon}{\varphi}(x)(y)) \\
 & = & \cons(a,\lcp(x,y)),
\end{eqnarray*}$$
and if $a \neq b$ we have
$$\begin{eqnarray*}
 &   & \lcp(\cons(a,x),\cons(b,y)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(b,y)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(b,y)) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> lcp :: (List t, Equal a) => t a -> t a -> t a
> lcp x y = case uncons x of
>   Left ()     -> nil
>   Right (a,u) -> case uncons y of
>     Left ()     -> nil
>     Right (b,v) -> if eq a b
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
2. We proceed by list induction on $z$. For the base case $z = \nil$, note that $\prefix(\nil,x)$, $\prefix(\nil,y)$, and $\prefix(\nil,\lcp(x,y))$ are all $\btrue$. For the inductive step, suppose the result holds for all $x$ and $y$ for some $z$ and let $a \in A$. Suppose further that $\prefix(\cons(a,z),x)$ and $\prefix(\cons(a,z),y)$. Then we must have $x = \cons(a,u)$ and $y = \cons(a,v)$, and thus $\prefix(z,u)$ and $\prefix(z,v)$ are both $\btrue$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \prefix(\cons(a,z),\lcp(x,y)) \\
 & = & \prefix(\cons(a,z),\lcp(\cons(a,u),\cons(a,v))) \\
 & = & \prefix(\cons(a,z),\cons(a,\lcp(u,v))) \\
 & = & \prefix(z,\lcp(u,v)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
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
3. Let $h = \lcp(\lcp(x,y),z)$, $k = \lcp(x,\lcp(y,z))$, $u = \lcp(x,y)$, and $v = \lcp(y,z)$. First we show that $\prefix(h,k)$. Note that $\prefix(h,u)$, so that $\prefix(h,x)$ and $\prefix(h,y)$. Now $\prefix(h,z)$, so that $\prefix(h,v)$. Thus $\prefix(h,k)$. The proof that $\prefix(k,h)$ is similar; thus $h = k$ as claimed.
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
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(x,u),\zip(y,v)) \\
 & = & \lcp(\zip(\nil,u),\zip(y,v)) \\
 & = & \lcp(\nil,\zip(y,v)) \\
 & = & \nil \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \zip(\lcp(\nil,y),\lcp(u,v)) \\
 & = & \zip(\lcp(x,y),\lcp(u,v))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(\nil,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\nil) \\
 & = & \nil \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),\nil),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v))
\end{eqnarray*}$$
as claimed. If $u = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),\nil),\zip(y,v)) \\
 & = & \lcp(\nil,\zip(y,v)) \\
 & = & \nil \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(\nil,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed. If $v = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,\nil)) \\
 & = & \lcp(\zip(\cons(a,x),u),\nil) \\
 & = & \nil \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,\nil)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed. Thus we can say $y = \cons(c,w)$, $u = \cons(b,h)$, and $v = \cons(d,k)$. If $a \neq c$, we have
$$\begin{eqnarray*}
 &   & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),\cons(c,w)),\lcp(u,v)) \\
 & = & \zip(\nil,\lcp(u,v)) \\
 & = & \nil \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,h)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
\end{eqnarray*}$$
as claimed. If $b \neq d$, we have
$$\begin{eqnarray*}
 &   & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(\cons(c,h),\cons(d,k))) \\
 & = & \zip(\lcp(\cons(a,x),y),\nil) \\
 & = & \nil \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,h)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\zip(\cons(a,x),u),\zip(y,v)) \\
\end{eqnarray*}$$
as claimed. Finally, suppose $a = c$ and $b = d$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \lcp(\zip(\cons(a,x),y),\zip(u,v)) \\
 & = & \lcp(\zip(\cons(a,x),\cons(b,w)),\zip(\cons(c,w),\cons(d,k))) \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((c,d),\zip(w,k))) \\
 & = & \lcp(\cons((a,b),\zip(x,h)),\cons((a,b),\zip(w,k))) \\
 & = & \cons((a,b),\lcp(\zip(x,h),\zip(w,k))) \\
 & = & \cons((a,b),\zip(\lcp(x,w),\lcp(h,k))) \\
 & = & \zip(\cons(a,\lcp(x,w)),\cons(b,\lcp(h,k))) \\
 & = & \zip(\lcp(\cons(a,x),\cons(a,w)),\lcp(\cons(b,h),\cons(b,k))) \\
 & = & \zip(\lcp(\cons(a,x),\cons(c,w)),\lcp(\cons(b,h),\cons(d,k))) \\
 & = & \zip(\lcp(\cons(a,x),y),\lcp(u,v)) \\
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\lcp$ interacts with $\map(f)$ if $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ an injective map. For all $x,y \in \lists{A}$ we have $$\map(f)(\lcp(x,y)) = \lcp(\map(f)(x),\map(f)(y)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$ we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(x,y)) \\
 & = & \map(f)(\lcp(\nil,y)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \lcp(\nil,\map(f)(y)) \\
 & = & \lcp(\map(f)(\nil),\map(f)(y)) \\
 & = & \lcp(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as needed. Suppose now the equality holds for some $x$ and let $a \in A$. We consider two possitiblities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\nil)) \\
 & = & \map(f)(\nil) \\
 & = & \nil \\
 & = & \lcp(\map(f)(\cons(a,x)),\nil) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\nil)) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed. Suppose then that $y = \cons(b,u)$. If $a = b$, we have $f(a) = f(b)$. Now
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(a,u))) \\
 & = & \map(f)(\cons(a,\lcp(x,u))) \\
 & = & \cons(f(a),\map(f)(\lcp(x,u))) \\
 & = & \cons(f(a),\lcp(\map(f)(x),\map(f)(u))) \\
 & = & \lcp(\cons(f(a),\map(f)(x)),\cons(f(a),\map(f)(u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(a,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(b,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed. On the other hand, if $a \neq b$, then (since $f$ is injective) $f(a) \neq f(b)$. Then we have
$$\begin{eqnarray*}
 &   & \map(f)(\lcp(\cons(a,x),y)) \\
 & = & \map(f)(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \map(f)(\lcp(x,u)) \\
 & = & \lcp(\map(f)(x),\map(f)(u)) \\
 & = & \lcp(\cons(f(a),\map(f)(x)),\cons(f(b),\map(f)(u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(\cons(b,u))) \\
 & = & \lcp(\map(f)(\cons(a,x)),\map(f)(y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

We can define the dual operation, longest common suffix, in terms of $\lcp$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define $\lcs : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\lcs(x,y) = \rev(\lcp(\rev(x),\rev(y))).$$

In Haskell:

> lcs :: (List t, Equal a) => t a -> t a -> t a
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
1. Note that
$$\begin{eqnarray*}
 &   & \suffix(\lcs(x,y),x) \\
 & = & \prefix(\rev(\lcs(x,y)),\rev(x)) \\
 & = & \prefix(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(x)) \\
 & = & \prefix(\lcp(\rev(x),\rev(y)),\rev(x)) \\
 & = & \btrue,
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \suffix(\lcs(x,y),y) \\
 & = & \prefix(\rev(\lcs(x,y)),\rev(y)) \\
 & = & \prefix(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(y)) \\
 & = & \prefix(\lcp(\rev(x),\rev(y)),\rev(y)) \\
 & = & \btrue,
\end{eqnarray*}$$
2. Suppose $\suffix(z,x)$ and $\suffix(z,y)$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \suffix(z,x) \\
 & = & \prefix(\rev(z),\rev(x))
\end{eqnarray*}$$
and likewise
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \suffix(z,y) \\
 & = & \prefix(\rev(z),\rev(y)).
\end{eqnarray*}$$
So we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \prefix(\rev(z),\lcp(\rev(x),\rev(y))) \\
 & = & \prefix(\rev(z),\rev(\rev(\lcp(\rev(x),\rev(y))))) \\
 & = & \prefix(\rev(z),\rev(\lcs(x,y))) \\
 & = & \suffix(z,\lcs(x,y))
\end{eqnarray*}$$
as claimed.
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
1. Note that
$$\begin{eqnarray*}
 &   & \lcs(x,x) \\
 & = & \rev(\lcp(\rev(x),\rev(x))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \lcs(x,y) \\
 & = & \rev(\lcp(\rev(x),\rev(y))) \\
 & = & \rev(\lcp(\rev(y),\rev(x))) \\
 & = & \lcs(y,x)
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \lcs(\lcs(x,y),z) \\
 & = & \lcs(\rev(\lcp(\rev(x),\rev(y))),z) \\
 & = & \rev(\lcp(\rev(\rev(\lcp(\rev(x),\rev(y)))),\rev(z)) \\
 & = & \rev(\lcp(\lcp(\rev(x),\rev(y)),\rev(z))) \\
 & = & \rev(\lcp(\rev(x),\lcp(\rev(y),\rev(z)))) \\
 & = & \rev(\lcp(\rev(x),\rev(\rev(\lcp(\rev(y),\rev(z)))))) \\
 & = & \rev(\lcp(\rev(x),\rev(\lcs(y,z)))) \\
 & = & \lcs(x,\lcs(y,z))
\end{eqnarray*}$$
as claimed.
4. Note that
$$\begin{eqnarray*}
 &   & \lcs(\cat(x,z),\cat(y,z)) \\
 & = & \rev(\lcp(\rev(\cat(x,z)),\rev(\cat(y,z)))) \\
 & = & \rev(\lcp(\cat(\rev(z),\rev(x)),\cat(\rev(z),\rev(y)))) \\
 & = & \rev(\cat(\rev(z),\lcp(\rev(x),\rev(y)))) \\
 & = & \cat(\rev(\lcp(\rev(x),\rev(y))),\rev(\rev(z))) \\
 & = & \cat(\lcs(x,y),z)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\lcs$ detects suffixes:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. Then $\lcs(x,y) = x$ if and only if $\suffix(x,y)$.
</p></div>

<div class="proof"><p>
Note that $$\lcs(x,y) = x$$ if and only if $$\rev(\lcp(\rev(x),\rev(y))) = x$$ if and only if $$\rev(\rev(\lcp(\rev(x),\rev(y)))) = \rev(x)$$ if and only if $$\lcp(\rev(x),\rev(y)) = \rev(x)$$ if and only if $$\prefix(\rev(x),\rev(y)) = \btrue$$ if and only if $$\suffix(x,y) = \btrue$$ as claimed.
</p></div>
</div>

And $\lcs$ cooperates with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$ and $a,b \in A$ we have $$\lcs(\snoc(a,x),\snoc(b,y)) = \left\{\begin{array}{ll} \snoc(a,\lcs(x,y)) & \mathrm{if}\ a = b \\ \nil & \mathrm{if}\ a \neq b. \end{array}\right.$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \lcs(\snoc(a,x),\snoc(b,y)) \\
 & = & \rev(\lcp(\rev(\snoc(a,x)),\rev(\snoc(b,y))) \\
 & = & \rev(\lcp(\cons(a,\rev(x)),\cons(b,\rev(y)) \\
 & = & Q.
\end{eqnarray*}$$
If $a = b$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \rev(\cons(a,\lcp(\rev(x),\rev(y)))) \\
 & = & \snoc(a,\rev(\lcp(\rev(x),\rev(y)))) \\
 & = & \snoc(a,\lcs(x,y))
\end{eqnarray*}$$
as claimed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And $\lcs$ also interacts with $\map(f)$ if $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ an injective map. For all $x,y \in \lists{A}$ we have $$\map(f)(\lcs(x,y)) = \lcs(\map(f)(x),\map(f)(y)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \map(f)(\lcs(x,y)) \\
 & = & \map(f)(\rev(\lcp(\rev(x),\rev(y)))) \\
 & = & \rev(\map(f)(\lcp(\rev(x),\rev(y)))) \\
 & = & \rev(\lcp(\map(f)(\rev(x)),\map(f)(\rev(y)))) \\
 & = & \rev(\lcp(\rev(\map(f)(x)),\rev(\map(f)(y)))) \\
 & = & \lcs(\map(f)(x),\map(f)(y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\lcp$:

> _test_lcp_alt :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_alt _ =
>   testName "lcp(x,y) == lcp'(x,y)" $
>   \x y -> eq (lcp x y) (lcp' x y)
> 
> 
> _test_lcp_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcp_idempotent _ =
>   testName "lcp(x,x) == x" $
>   \x -> eq (lcp x x) x
> 
> 
> _test_lcp_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_commutative _ =
>   testName "lcp(x,y) == lcp(y,x)" $
>   \x y -> eq (lcp x y) (lcp y x)
> 
> 
> _test_lcp_associative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcp_associative _ =
>   testName "lcp(lcp(x,y),z) == lcp(x,lcp(y,z))" $
>   \x y z -> eq (lcp (lcp x y) z) (lcp x (lcp y z))
> 
> 
> _test_lcp_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcp_cat _ =
>   testName "cat(x,lcp(y,z)) == lcp(cat(x,y),cat(x,z))" $
>   \x y z -> eq (cat x (lcp y z)) (lcp (cat x y) (cat x z))
> 
> 
> _test_lcp_prefix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcp_prefix _ =
>   testName "lcp(x,y) == x iff prefix(x,y)" $
>   \x y -> eq (eq (lcp x y) x) (prefix x y)
> 
> 
> _test_lcp_zip :: (List t, Equal a, Equal (t (a,a)))
>   => t a -> Test (t a -> t a -> t a -> t a -> Bool)
> _test_lcp_zip _ =
>   testName "zip(lcp(x,y),lcp(u,v)) == lcp(zip(x,u),zip(y,v))" $
>   \x y u v -> eq (zip (lcp x y) (lcp u v)) (lcp (zip x u) (zip y v))

Tests for $\lcs$:

> _test_lcs_idempotent :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_lcs_idempotent _ =
>   testName "lcs(x,x) == x" $
>   \x -> eq (lcs x x) x
> 
> 
> _test_lcs_commutative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcs_commutative _ =
>   testName "lcs(x,y) == lcs(y,x)" $
>   \x y -> eq (lcs x y) (lcs y x)
> 
> 
> _test_lcs_associative :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcs_associative _ =
>   testName "lcs(lcs(x,y),z) == lcs(x,lcs(y,z))" $
>   \x y z -> eq (lcs (lcs x y) z) (lcs x (lcs y z))
> 
> 
> _test_lcs_cat :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> t a -> Bool)
> _test_lcs_cat _ =
>   testName "cat(lcs(x,y),z) == lcs(cat(x,z),cat(y,z))" $
>   \x y z -> eq (cat (lcs x y) z) (lcs (cat x z) (cat y z))
> 
> 
> _test_lcs_suffix :: (List t, Equal a, Equal (t a))
>   => t a -> Test (t a -> t a -> Bool)
> _test_lcs_suffix _ =
>   testName "lcs(x,y) == x <==> suffix(x,y)" $
>   \x y -> eq (eq (lcs x y) x) (suffix x y)

And the suite:

> -- run all tests for lcp and lcs
> _test_lcp ::
>   ( TypeName a, Equal a, Show a, Arbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a))
>   ) => t a -> Int -> Int -> IO ()
> _test_lcp t maxSize numCases = do
>   testLabel ("lcp & lcs: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_lcp_alt t)
>   runTest args (_test_lcp_idempotent t)
>   runTest args (_test_lcp_commutative t)
>   runTest args (_test_lcp_associative t)
>   runTest args (_test_lcp_cat t)
>   runTest args (_test_lcp_prefix t)
>   runTest args (_test_lcp_zip t)
> 
>   runTest args (_test_lcs_idempotent t)
>   runTest args (_test_lcs_commutative t)
>   runTest args (_test_lcs_associative t)
>   runTest args (_test_lcs_cat t)
>   runTest args (_test_lcs_suffix t)

And ``main``:

> main_lcp :: IO ()
> main_lcp = do
>   _test_lcp (nil :: ConsList Bool)  20 100
>   _test_lcp (nil :: ConsList Unary) 20 100
