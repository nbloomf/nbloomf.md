---
title: All and Any
author: nbloomf
date: 2017-05-10
tags: arithmetic-made-difficult, literate-haskell
slug: all-any
---

> module AllAndAny
>   ( all, any, _test_all_any, main_all_any
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import Lists
> import Reverse
> import Map
> import Cat
> import Zip
> import Prefix
> 
> import Prelude (const)
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define two boolean functions for lists called $\all$ and $\any$. Each one takes as an argument a predicate $A \rightarrow \bool$, and then tests whether all or any of the items in a list of type $\lists{A}$ satisfy the predicate.

<div class="result">
<div class="defn"><p>
Define $\varphi : \bool^A \rightarrow A \times \bool \rightarrow \bool$ by $$\varphi(p)(a,q) = \band(p(a),q).$$ Now define $\all : \bool^A \times \lists{A} \rightarrow \bool$ by $$\all(p,x) = \foldr{\btrue}{\varphi(p)}(x).$$
</p></div>
</div>

We can translate $\all$ to Haskell directly as follows:

> all' :: (List t) => (a -> Bool) -> t a -> Bool
> all' p = foldr True (phi p)
>   where
>     phi p a q = and (p a) q

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $p : A \rightarrow \bool$, $a \in A$, and $x \in \lists{A}$, we have the following.

1. $\all(p,\nil) = \btrue$.
2. $\all(p,\cons(a,x)) = \band(p(a),\all(p,x))$.
3. $\all(p,\snoc(a,x)) = \band(p(a),\all(p,x))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \all(p,\nil) \\
 & = & \foldr{\btrue}{\varphi(p)}(\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \all(p,\cons(a,x)) \\
 & = & \foldr{\btrue}{\varphi(p)}(\cons(a,x)) \\
 & = & \varphi(p)(a,\foldr{\btrue}{\varphi(p)}(x)) \\
 & = & \band(p(a),\foldr{\btrue}{\varphi(p)}(x)) \\
 & = & \band(p(a),\all(p,x))
\end{eqnarray*}$$
as claimed.
3. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\snoc(a,x)) \\
 & = & \all(p,\snoc(a,\nil)) \\
 & = & \all(p,\cons(a,\nil)) \\
 & = & \band(p(a),\all(p,\nil)) \\
 & = & \band(p(a),\all(p,x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $p$ and $a$ for some $x$ and let $b \in A$. Using the inductive step, we have
$$\begin{eqnarray*}
 &   & \all(p,\snoc(a,\cons(b,x))) \\
 & = & \all(p,\cons(b,\snoc(a,x))) \\
 & = & \band(p(b),\all(p,\snoc(a,x))) \\
 & = & \band(p(b),\band(p(a),\all(p,x))) \\
 & = & \band(p(a),\band(p(b),\all(p,x))) \\
 & = & \band(p(a),\all(p,\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

In Haskell:

> all :: (List t) => (a -> Bool) -> t a -> Bool
> all p x = case uncons x of
>   Left ()     -> True
>   Right (a,w) -> and (p a) (all p w)

As a corollary:

<div class="result">
<div class="corollary"><p>
$$\all(p,x) = \foldr{\btrue}{\band}(\map(p)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,x) \\
 & = & \all(p,\nil) \\
 & = & \btrue \\
 & = & \foldr{\btrue}{\band}(\nil) \\
 & = & \foldr{\btrue}{\band}(\map(p)(\nil)) \\
 & = & \foldr{\btrue}{\band}(\map(p)(x))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p,\cons(a,x)) \\
 & = & \band(p(a),\all(p,x)) \\
 & = & \band(p(a),\foldr{\btrue}{\band}(\map(p)(x))) \\
 & = & \foldr{\btrue}{\band}(\cons(p(a),\map(p)(x))) \\
 & = & \foldr{\btrue}{\band}(\map(p)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now $\all$ satisfies some nice properties.

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$. Then the following hold for all $x,y \in \lists{A}$.

1. $\all(\const(\btrue),x) = \btrue$.
2. If $x \neq \nil$, then $\all(\const(\bfalse),x) = \bfalse$.
3. $\all(p,\cat(x,y)) = \band(\all(p)(x),\all(p)(y))$.
4. $\all(p,\rev(x)) = \all(p,x)$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\const(\btrue),x) \\
 & = & \all(\const(\btrue),\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(\const(\btrue),\cons(a,x)) \\
 & = & \band(\const(\btrue)(a),\all(\const(\btrue),x)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. Say $x = \cons(a,u)$. Now
$$\begin{eqnarray*}
 &   & \all(\const(\bfalse),x) \\
 & = & \all(\const(\bfalse),\cons(a,u)) \\
 & = & \band(\const(\bfalse)(a),\all(\const(\bfalse),u)) \\
 & = & \band(\bfalse,\all(\const(\bfalse),u)) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\cat(x,y)) \\
 & = & \all(p,\cat(\nil,y)) \\
 & = & \all(p,y) \\
 & = & \band(\btrue,\all(p,y)) \\
 & = & \band(\all(p,\nil),\all(p,y)) \\
 & = & \band(\all(p,x),\all(p,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p,\cat(\cons(a,x),y)) \\
 & = & \all(p,\cons(a,\cat(x,y))) \\
 & = & \band(p(a),\all(p,\cat(x,y))) \\
 & = & \band(p(a),\band(\all(p,x),\all(p,y))) \\
 & = & \band(\band(p(a),\all(p,x)),\all(p,y)) \\
 & = & \band(\all(p,\cons(a,x)),\all(p,y))
\end{eqnarray*}$$
as needed.
4. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\rev(x)) \\
 & = & \all(p,\rev(\nil)) \\
 & = & \all(p,\nil) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \all(p,\rev(\cons(a,x))) \\
 & = & \all(p,\rev(\cat(\cons(a,\nil),x))) \\
 & = & \all(p,\cat(\rev(x),\rev(\cons(a,\nil)))) \\
 & = & \band(\all(p,\rev(x)),\all(p,\rev(\cons(a,\nil)))) \\
 & = & \band(\all(p,x),\all(p,\cons(a,\nil))) \\
 & = & \band(\all(p,\cons(a,\nil)),\all(p,x)) \\
 & = & \all(p,\cat(\cons(a,\nil),x)) \\
 & = & \all(p,\cons(a,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

And another:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p,q : A \rightarrow \bool$. If $p(a)$ implies $q(a)$ for all $a \in A$, then if $$\all(p,x) = \btrue,$$ then $$\all(q,x) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have $$\all(p,x) = \all(p,\nil) = \btrue$$ and $$\all(q,x) = \all(q,\nil) = \btrue$$, which is sufficient. For the inductive step, suppose the implication holds for all $p$ and $q$ for some $x$ and let $a \in A$. Suppose further that $$\all(p,\cons(a,x)) = \btrue.$$ In particular, we have $$\band(p(a),\all(p,x)) = \btrue,$$ so that $p(a) = \btrue$ and $\all(p,x) = \btrue$. Now $q(a) = \btrue$, and we have
$$\begin{eqnarray*}
 &   & \all(q,\cons(a,x)) \\
 & = & \band(q(a),\all(q,x)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

One more.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ and $p : B \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\all(p,\map(f)(x)) = \all(p \circ f,x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(p,\map(f)(x)) \\
 & = & \all(p,\map(f)(\nil)) \\
 & = & \all(p,\nil) \\
 & = & \btrue \\
 & = & \all(p \circ f,\nil) \\
 & = & \all(p \circ f,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \all(p,\map(f)(\cons(a,x))) \\
 & = & \all(p,\cons(f(a),\map(f)(x))) \\
 & = & \band(p(f(a)),\all(p,\map(f)(x))) \\
 & = & \band((p \circ f)(a),\all(p \circ f,x)) \\
 & = & \all(p \circ f,\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\any$ is very similar.

<div class="result">
<div class="defn"><p>
Define $\varphi : \bool^A \rightarrow A \times \bool \rightarrow \bool$ by $$\varphi(p)(a,q) = \bor(p(a),q).$$ Now define $\any : \bool^A \times \lists{A} \rightarrow \bool$ by $$\any(p,x) = \foldr{\bfalse}{\varphi(p)}(x).$$
</p></div>
</div>

We can translate $\any$ to Haskell directly as follows:

> any' :: (List t) => (a -> Bool) -> t a -> Bool
> any' p = foldr False (phi p)
>   where
>     phi p a q = or (p a) q

The following result suggests a more straightforward implementation:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $p : A \rightarrow \bool$. The following hold for all $x \in \lists{A}$ and $a \in A$.

1. $\any(p,\nil) = \bfalse$.
2. $\any(p,\cons(a,x)) = \bor(p(a),\any(p,x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \any(p,\nil) \\
 & = & \foldr{\bfalse}{\varphi(p)}(\nil) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \any(p,\cons(a,x)) \\
 & = & \foldr{\bfalse}{\varphi(p)}(\cons(a,x)) \\
 & = & \varphi(p)(a,\foldr{\bfalse}{\varphi(p)}(x)) \\
 & = & \bor(p(a),\foldr{\bfalse}{\varphi(p)}(x)) \\
 & = & \bor(p(a),\any(p,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

> any :: (List t) => (a -> Bool) -> t a -> Bool
> any p x = case uncons x of
>   Left ()     -> False
>   Right (a,w) -> or (p a) (any p w)

And a corollary.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set with $p : A \rightarrow \bool$. Then the following hold for all $x \in \lists{A}$.

1. $\any(p,x) = \foldr{\bfalse}{\bor}(\map(p)(x))$.
2. $\any(p,x) = \bnot(\all(\bnot \circ p,x))$.
3. $\all(p,x) = \bnot(\any(\bnot \circ p,x))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \any(p,x) \\
 & = & \any(p,\nil) \\
 & = & \bfalse \\
 & = & \foldr{\bfalse}{\bor}(\nil) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(\nil)) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \any(p,\cons(a,x)) \\
 & = & \bor(p(a),\any(x)) \\
 & = & \bor(p(a),\foldr{\bfalse}{\bor}(\map(p)(x))) \\
 & = & \foldr{\bfalse}{\bor}(\cons(p(a),\map(p)(x))) \\
 & = & \foldr{\bfalse}{\bor}(\map(p)(\cons(a,x)))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \bnot(\all(\not \circ p,x)) \\
 & = & \bnot(\all(\not \circ p,\nil)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse \\
 & = & \foldr{\bfalse}{\varphi(p)}(\nil) \\
 & = & \foldr{\bfalse}{\varphi(p)}(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \bnot(\all(\bnot \circ p,\cons(a,x))) \\
 & = & \bnot(\band(\bnot(p(a)),\all(\bnot \circ p,x))) \\
 & = & \bor(\bnot(\bnot(p(a))),\bnot(\all(\bnot \circ p,x))) \\
 & = & \bor(p(a),\any(p,x)) \\
 & = & \any(p,\cons(a,x))
\end{eqnarray*}$$
as needed.
3. Note that
$$\begin{eqnarray*}
 &   & \bnot(\any(\bnot \circ p,x)) \\
 & = & \bnot(\bnot(\all(\bnot \circ \bnot \circ p,x))) \\
 & = & \all(p,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

more stuff

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$. Then the following hold for all $x,y \in \lists{A}$.

1. $\any(\const(\bfalse),x) = \bfalse$.
2. If $x \neq \nil$, then $\any(\const(\btrue),x) = \btrue$.
3. $\any(p,\cat(x,y)) = \bor(\any(p)(x),\any(p)(y))$.
4. $\any(p,\rev(x)) = \any(p,x)$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \any(\const(\bfalse),x) \\
 & = & \bnot(\all(\bnot \circ \const(\bfalse),x)) \\
 & = & \bnot(\all(\const(\btrue),x)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \any(\const(\btrue),x) \\
 & = & \all(\bnot \circ \const(\btrue),x) \\
 & = & \all(\const(\bnot(\btrue)),x) \\
 & = & \all(\const(\bfalse),x) \\
 & = & \bfalse
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \any(p,\cat(x,y)) \\
 & = & \bnot(\all(\bnot \circ p,\cat(x,y))) \\
 & = & \bnot(\band(\all(\bnot \circ p,x),\all(\bnot \circ p,y))) \\
 & = & \bor(\bnot(\all(\bnot \circ p,x)),\bnot(\all(\bnot \circ p,y))) \\
 & = & \bor(\any(p,x),\any(p,y))
\end{eqnarray*}$$
as claimed.
4. Note that
$$\begin{eqnarray*}
 &   & \any(p,\rev(x)) \\
 & = & \bnot(\all(\bnot \circ p,\rev(x))) \\
 & = & \bnot(\all(\bnot \circ p,x)) \\
 & = & \any(p,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

One more.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ and $p : B \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\any(p,\map(f)(x)) = \any(p \circ f,x).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \any(p,\map(f)(x)) \\
 & = & \bnot(\all(\bnot \circ p,\map(f)(x))) \\
 & = & \bnot(\all((\bnot \circ p) \circ f,x)) \\
 & = & \bnot(\all(\bnot \circ (p \circ f),x)) \\
 & = & \any(p \circ f,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\all$:

> _test_all_alt :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_all_alt _ =
>   testName "all(p,x) == all'(p,x)" $
>   \p x -> eq (all p x) (all' p x)
> 
> 
> _test_all_mapfold :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_all_mapfold _ =
>   testName "all(p,x) == foldr(true,and)(map(p)(x))" $
>   \p x -> eq (all p x) (foldr True and (map p x))
> 
> 
> _test_all_not_any :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_all_not_any _ =
>   testName "all(p,x) == not(any(not . p, x))" $
>   \p x -> eq (all p x) (not (any (not . p) x))
> 
> 
> _test_all_const_true :: (List t, Equal a)
>   => t a -> Test (t a -> Bool)
> _test_all_const_true _ =
>   testName "all(const(true),x) == true" $
>   \x -> eq (all (const True) x) True
> 
> 
> _test_all_cat :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_all_cat _ =
>   testName "all(p,cat(x,y)) == all(p,x) && all(p,y)" $
>   \p x y -> eq (all p (cat x y)) (and (all p x) (all p y))
> 
> 
> _test_all_rev :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_all_rev _ =
>   testName "all(p,rev(x)) == all(p,x)" $
>   \p x y -> eq (all p (rev x)) (all p x)

Tests for $\any$:

> _test_any_alt :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_any_alt _ =
>   testName "any(p,x) == any'(p,x)" $
>   \p x -> eq (any p x) (any' p x)
> 
> 
> _test_any_mapfold :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_any_mapfold _ =
>   testName "any(p,x) == foldr(false,or)(map(p)(x))" $
>   \p x -> eq (any p x) (foldr False or (map p x))
> 
> 
> _test_any_not_all :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_any_not_all _ =
>   testName "any(p,x) == not(all(not . p, x))" $
>   \p x -> eq (any p x) (not (all (not . p) x))
> 
> 
> _test_any_const_false :: (List t, Equal a)
>   => t a -> Test (t a -> Bool)
> _test_any_const_false _ =
>   testName "any(const(false),x) == false" $
>   \x -> eq (any (const False) x) False
> 
> 
> _test_any_cat :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_any_cat _ =
>   testName "any(p,cat(x,y)) == any(p,x) || any(p,y)" $
>   \p x y -> eq (any p (cat x y)) (or (any p x) (any p y))
> 
> 
> _test_any_rev :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> t a -> Bool)
> _test_any_rev _ =
>   testName "any(p,rev(x)) == any(p,x)" $
>   \p x y -> eq (any p (rev x)) (any p x)

And the suite:

> -- run all tests for all and any
> _test_all_any ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_all_any t maxSize numCases = do
>   testLabel ("all & any: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_all_alt t)
>   runTest args (_test_all_mapfold t)
>   runTest args (_test_all_not_any t)
>   runTest args (_test_all_const_true t)
>   runTest args (_test_all_cat t)
>   runTest args (_test_all_rev t)
> 
>   runTest args (_test_any_alt t)
>   runTest args (_test_any_mapfold t)
>   runTest args (_test_any_not_all t)
>   runTest args (_test_any_const_false t)
>   runTest args (_test_any_cat t)
>   runTest args (_test_any_rev t)

And ``main``:

> main_all_any :: IO ()
> main_all_any = do
>   _test_all_any (nil :: ConsList Bool)  20 100
>   _test_all_any (nil :: ConsList Unary) 20 100
