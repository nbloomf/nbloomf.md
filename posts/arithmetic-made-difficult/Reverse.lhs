---
title: Reverse
author: nbloomf
date: 2017-04-24
tags: arithmetic-made-difficult, literate-haskell
slug: rev
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Reverse
>   ( revcat, rev, _test_rev, main_rev
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import LeftFold
> import Snoc

Today we'll define a function that takes a list and reverses the order of its elements; say, to turn $(a,b,c)$ into $(c,b,a)$ and vice versa.

First we define a utility as follows.

:::::: definition ::
Let $A$ be a set, and define $\varphi : \lists{A} \times A \rightarrow \lists{A}$ by $\varphi(x,a) = \cons(a,x)$. We now define a map $\revcat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\revcat = \foldl{\varphi}.$$

In Haskell:

> revcat :: (List t) => t a -> t a -> t a
> revcat = foldl phi
>   where
>     phi x a = cons a x

::::::::::::::::::::

Since $\revcat$ is defined as a $\foldl{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\revcat$ is the unique solution $f : \lists{A} \times \lists{A} \rightarrow \lists{A}$ to the following system of equations for all $a \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(x,\nil) = x \\
 f(x,\cons(a,y)) = f(\cons(a,x),y)
\end{array}\right.$$

::: test :::::::::::

> _test_revcat_nil :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_revcat_nil z =
>   testName "revcat(x,nil) == x" $
>   \x ->
>     let nil' = nil `withTypeOf` z in
>     eq (revcat x nil') x
> 
> 
> _test_revcat_cons :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_revcat_cons _ =
>   testName "revcat(x,cons(a,y)) == revcat(cons(a,x),y)" $
>   \a x y -> eq (revcat x (cons a y)) (revcat (cons a x) y)

::::::::::::::::::::
::::::::::::::::::::

Now $\revcat$ interacts with $\snoc$.

:::::: theorem :::::
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have the following.

1. $\revcat(\snoc(a,x),y) = \snoc(a,\revcat(x,y))$.
2. $\revcat(x,\snoc(a,y)) = \cons(a,\revcat(x,y))$.

::: proof ::::::::::
1. We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \revcat(\snoc(a,x),\nil) \\
 & = & \snoc(a,x) \\
 & = & \snoc(a,\revcat(x,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $x$ for some $y$, and let $b \in A$. Now we have
$$\begin{eqnarray*}
 &   & \revcat(\snoc(a,x),\cons(b,y)) \\
 & = & \revcat(\cons(b,\snoc(a,x)),y) \\
 & = & \revcat(\snoc(a,\cons(b,x)),y) \\
 & = & \snoc(a,\revcat(\cons(b,x)),y) \\
 & = & \snoc(a,\revcat(x,\const(b,y)))
\end{eqnarray*}$$
as needed.
2. We proceed by list induction on $y$. For the base case $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \revcat(x,\snoc(a,\nil)) \\
 & = & \revcat(x,\cons(a,\nil)) \\
 & = & \revcat(\cons(a,x),\nil) \\
 & = & \cons(a,x) \\
 & = & \cons(a,\revcat(x,\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $x$ for some $y$, and let $b \in A$. Now we have
$$\begin{eqnarray*}
 &   & \revcat(x,\snoc(a,\cons(b,y))) \\
 & = & \revcat(x,\cons(b,\snoc(a,y))) \\
 & = & \revcat(\cons(b,x),\snoc(a,y)) \\
 & = & \cons(a,\revcat(\cons(b,x),y)) \\
 & = & \cons(a,\revcat(x,\cons(b,y)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_revcat_snoc_left :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_revcat_snoc_left _ =
>   testName "revcat(snoc(a,x),y) == snoc(a,revcat(x,y))" $
>   \a x y -> eq (revcat (snoc a x) y) (snoc a (revcat x y))
> 
> 
> _test_revcat_snoc_right :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> t a -> Bool)
> _test_revcat_snoc_right _ =
>   testName "revcat(x,snoc(a,y)) == cons(a,revcat(x,y))" $
>   \a x y -> eq (revcat x (snoc a y)) (cons a (revcat x y))

::::::::::::::::::::
::::::::::::::::::::

And we define list reversal in terms of $\revcat$.

:::::: definition ::
Let $A$ be a set. We define $\rev : \lists{A} \rightarrow \lists{A}$ by $$\rev(x) = \revcat(\nil,x).$$

In Haskell:

> rev :: (List t) => t a -> t a
> rev = revcat nil

::::::::::::::::::::

Now $\rev$ is essentially defined here as a left fold, but it can also be characterized as a right fold.

:::::: theorem :::::
We have $$\rev(x) = \foldr{\nil}{\snoc}(x).$$

::: proof ::::::::::
Let $\varphi$ be as defined in the definition of $\rev$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\snoc}(\nil) \\
 &     \href{@lists@#def-foldr-nil}
   = & \nil \\
 & = & \revcat(\nil,\nil) \\
 & = & \rev(\nil).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\snoc}(\cons(a,x)) \\
 &     \href{@lists@#def-foldr-cons}
   = & \snoc(a,\foldr{\nil}{\snoc}(x)) \\
 & = & \snoc(a,\rev(x)) \\
 & = & \snoc(a,\revcat(\nil,x)) \\
 & = & \revcat(\snoc(a,\nil),x) \\
 & = & \revcat(\cons(a,\nil),x) \\
 & = & \revcat(\nil,\cons(a,x)) \\
 & = & \rev(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_foldr :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_rev_foldr _ =
>   testName "rev(x) == foldr(nil,snoc)(x)" $
>   \x -> eq (rev x) (foldr nil snoc x)

::::::::::::::::::::
::::::::::::::::::::

Because $\rev$ is equivalent to a $\foldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. Then $\rev$ is the unique function $f : \lists{A} \rightarrow \lists{A}$ having the property that for all $a \in A$ and $x \in \lists{A}$ we have
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \snoc(a,f(x)).
\end{array}\right.$$

::: test :::::::::::

> _test_rev_nil :: (List t, Equal (t a))
>   => t a -> Test Bool
> _test_rev_nil z =
>   testName "rev(nil) == nil" $
>     let nil' = nil `withTypeOf` z in
>     eq (rev nil') nil'
> 
> 
> _test_rev_cons :: (List t, Equal (t a))
>   => t a -> Test (a -> t a -> Bool)
> _test_rev_cons _ =
>   testName "rev(cons(a,x)) == snoc(a,rev(x))" $
>   \a x -> eq (rev (cons a x)) (snoc a (rev x))

::::::::::::::::::::
::::::::::::::::::::

Special cases:

:::::: theorem :::::
Let $A$ be a set. For all $a,b \in A$ we have the following.

1. $\rev(\cons(a,\nil)) = \cons(a,\nil)$.
2. $\rev(\cons(a,\cons(b,\nil))) = \cons(b,\cons(a,\nil))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \rev(\cons(a,\nil)) \\
 & = & \revcat(\nil,\cons(a,\nil)) \\
 & = & \revcat(\cons(a,\nil),\nil) \\
 & = & \cons(a,\nil)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \rev(\cons(a,\cons(b,\nil))) \\
 & = & \revcat(\nil,\cons(a,\cons(b,\nil))) \\
 & = & \revcat(\cons(a,\nil),\cons(b,\nil)) \\
 & = & \revcat(\cons(b,\cons(a,\nil)),\nil) \\
 & = & \cons(b,\cons(a,\nil))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_single :: (List t, Equal (t a))
>   => t a -> Test (a -> Bool)
> _test_rev_single z =
>   testName "rev(cons(a,nil)) == cons(a,nil)" $
>   \a ->
>     let nil' = nil `withTypeOf` z in
>     eq (rev (cons a nil')) (cons a nil')
> 
> 
> _test_rev_double :: (List t, Equal (t a))
>   => t a -> Test (a -> a -> Bool)
> _test_rev_double z =
>   testName "rev(cons(a,cons(b,nil))) == cons(b,cons(a,nil))" $
>   \a b ->
>     let nil' = nil `withTypeOf` z in
>     eq
>       (rev (cons a (cons b nil')))
>       (cons b (cons a nil'))

::::::::::::::::::::
::::::::::::::::::::

Now $\rev$ and $\snoc$ interact:

:::::: theorem :::::
Let $A$ be a set. Then for all $a \in A$ and $x \in \lists{A}$, we have $$\rev(\snoc(a,x)) = \cons(a,\rev(x)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \rev(\snoc(a,\nil)) \\
 & = & \revcat(\nil,\snoc(a,x)) \\
 & = & \cons(a,\revcat(\nil,x)) \\
 & = & \cons(a,\rev(x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_snoc :: (List t, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_rev_snoc _ =
>   testName "rev(snoc(a,x)) == cons(a,rev(x))" $
>   \a b x -> eq (rev (snoc a x)) (cons a (rev x))

::::::::::::::::::::
::::::::::::::::::::

And $\rev$ is an involution.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $\rev(\rev(x)) = x$.

::: proof ::::::::::
We proceed by list induction. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \rev(\rev(\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \rev(\rev(\cons(a,x))) \\
 & = & \rev(\snoc(a,\rev(x))) \\
 & = & \cons(a,\rev(\rev(x))) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_involution :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_rev_involution _ =
>   testName "rev(rev(x)) == x" $
>   \x -> eq (rev (rev x)) x

::::::::::::::::::::
::::::::::::::::::::

$\rev$ preserves $\isnil$ and $\beq$.

:::::: theorem :::::
Let $A$ be a set with $x,y \in \lists{A}$. Then we have the following.

1. $\isnil(x) = \isnil(\rev(x))$.
2. $\beq(x,y) = \beq(\rev(x),\rev(y))$.

::: proof ::::::::::
1. We consider two possibilities. If $x = \nil$, we have $$x = \nil = \rev(\nil) = \rev(x),$$ so that $\isnil(x) = \isnil(\rev(x))$ as claimed. Suppose instead that $x = \cons(a,u)$ for some $u$; then $x = \snoc(b,v)$ for some $v$. Now we have
$$\begin{eqnarray*}
 &   & \isnil(x) \\
 & = & \isnil(\cons(a,u)) \\
 & = & \bfalse \\
 & = & \isnil(\cons(b,\rev(v))) \\
 & = & \isnil(\rev(\snoc(b,v))) \\
 & = & \isnil(\rev(x))
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(x,y) \\
 & = & \beq(\nil,y) \\
 & = & \isnil(y) \\
 & = & \isnil(\rev(y)) \\
 & = & \beq(\nil,\rev(y)) \\
 & = & \beq(\rev(\nil),\rev(y)) \\
 & = & \beq(\rev(x),\rev(y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$ and let $a \in A$. We consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,x),y) \\
 & = & \beq(\cons(a,x),\nil) \\
 & = & \isnil(\cons(a,x)) \\
 & = & \isnil(\rev(\cons(a,x))) \\
 & = & \beq(\rev(\cons(a,x)),\nil) \\
 & = & \beq(\rev(\cons(a,x)),\rev(\nil)) \\
 & = & \beq(\rev(\cons(a,x)),\rev(y))
\end{eqnarray*}$$
as needed. Suppose instead that $y = \cons(b,u)$. Using the inductive hypothsis, we have
$$\begin{eqnarray*}
 &   & \beq(\cons(a,x),y) \\
 & = & \beq(\cons(a,x),\cons(b,u)) \\
 & = & \band(\beq(a,b),\beq(x,u)) \\
 & = & \band(\beq(a,b),\beq(\rev(x),\rev(u))) \\
 & = & \beq(\snoc(a,\rev(x)),\snoc(b,\rev(u))) \\
 & = & \beq(\rev(\cons(a,x)),\rev(\cons(b,u))) \\
 & = & \beq(\rev(\cons(a,x)),\rev(y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_isnil :: (List t, Equal (t a), Equal a)
>   => t a -> Test (t a -> Bool)
> _test_rev_isnil _ =
>   testName "isnil(rev(x)) == isnil(x)" $
>   \x -> eq (isNil (rev x)) (isNil x)
> 
> 
> _test_rev_eq :: (List t, Equal (t a), Equal a, Boolean b, Equal b)
>   => t a -> b -> Test (t a -> t a -> Bool)
> _test_rev_eq _ p =
>   testName "eq(rev(x),rev(y)) == eq(x,y)" $
>   \x y -> eq
>     (eq (rev x) (rev y))
>     ((eq x y) `withTypeOf` p)

::::::::::::::::::::
::::::::::::::::::::

And left fold is a reversed right fold.

:::::: theorem :::::
Let $\varphi : B \times A \rightarrow B$, and define $\psi : A \times B \rightarrow B$ by $$\psi(a,b) = \varphi(b,a).$$ Now $$\foldl{\varphi}(e,x) = \foldr{e,\psi}(\rev(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldl{\varphi}(e,\nil) \\
 & = & e \\
 &     \href{@lists@#def-foldr-nil}
   = & \foldr{e,\psi}(\nil) \\
 & = & \foldr{e,\psi}(\rev(\nil))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $e$ for some $x$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldl{\varphi}(e,\cons(a,x)) \\
 & = & \foldl{\varphi}(\varphi(e,a),x) \\
 & = & \foldr{\varphi(e,a)}{\psi}(\rev(x)) \\
 & = & \foldr{\psi(a,e)}{\psi}(\rev(x)) \\
 & = & \foldr{e}{\psi}(\snoc(a,\rev(x))) \\
 & = & \foldr{e}{\psi}(\rev(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_rev_foldl :: (List t, Equal (t a), Equal a)
>   => t a -> Test ((a -> a -> a) -> a -> t a -> Bool)
> _test_rev_foldl _ =
>   testName "foldl(phi)(e,x) == foldr(e,flip(phi))(rev(x))" $
>   \phi e x ->
>     let psi a b = phi b a in
>     eq (foldl phi e x) (foldr e psi (rev x))

::::::::::::::::::::
::::::::::::::::::::

Note that $\rev$ is a nontrivial involution on $\lists{A}$ -- in particular, that means it is a bijection on $\lists{A}$ other than the identity. When this happens on a type with an induction principle, if we can show that our nontrivial bijection is actually an isomorphism, we get an alternative induction principle (almost) for free. And indeed, $\rev$ is an isomorphism taking $\cons$ to $\snoc$.

:::::: theorem :::::
(Snoc Induction.) Let $A$ be a set, and let $f : \lists{A} \rightarrow B$ be a map. Suppose $C \subseteq B$ is a subset with the property that

1. $f(\nil) \in C$
2. If $f(x) \in C$ and $a \in A$, then $f(\snoc(a,x)) \in C$.

Then we have $f(x) \in C$ for all $x \in \lists{A}$.

::: proof ::::::::::
This proof is analogous to that of the ordinary list induction principle. Define $T \subseteq \lists{A}$ by $$T = \{ x \in \lists{A} \mid f(x) \in C \}.$$ Note that $\nil \in T$ and if $x \in T$ and $a \in A$ then $\snoc(a,x) \in T$; that is, $(T,\nil,\snoc)$ is an $A$-iterative set. We define $\Theta : \lists{A} \rightarrow T$ to be the fold $$\Theta = \foldr{\nil}{\snoc}.$$ Now $\rev : T \rightarrow \lists{A}$ is an $A$-iterative homomorphism since $$\rev(\cons(a,x)) = \snoc(a,\rev(x)).$$ Thus $\rev \circ \Theta$ is an $A$-inductive homomorphism, which by uniqueness must be the identity on $\lists{A}$. If $x \in \lists{A}$, we have $$x = \rev(\rev(x)) = \rev(\id(\rev(x))) = \rev(\rev(\Theta(\rev(x)))) = \Theta(\rev(x)) \in T,$$ so that $T = \lists{A}$ as claimed.
::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_rev ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   , TypeName b, Boolean b, Equal b
>   ) => t a -> b -> Int -> Int -> IO ()
> _test_rev t p maxSize numCases = do
>   testLabel1 "rev" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_revcat_nil t)
>   runTest args (_test_revcat_cons t)
>   runTest args (_test_revcat_snoc_left t)
>   runTest args (_test_revcat_snoc_right t)
>   runTest args (_test_rev_foldr t)
>   runTest args (_test_rev_nil t)
>   runTest args (_test_rev_cons t)
>   runTest args (_test_rev_single t)
>   runTest args (_test_rev_double t)
>   runTest args (_test_rev_snoc t)
>   runTest args (_test_rev_involution t)
>   runTest args (_test_rev_isnil t)
>   runTest args (_test_rev_eq t p)
>   runTest args (_test_rev_foldl t)

Main:

> main_rev :: IO ()
> main_rev = do
>   _test_rev (nil :: ConsList Bool)  (true :: Bool) 20 100
>   _test_rev (nil :: ConsList Unary) (true :: Bool) 20 100
