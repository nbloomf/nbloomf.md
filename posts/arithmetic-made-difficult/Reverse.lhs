---
title: Reverse
author: nbloomf
date: 2017-04-24
tags: arithmetic-made-difficult, literate-haskell
slug: rev
---

> module Reverse
>   ( revcat, rev, _test_rev, main_rev
>   ) where
> 
> import Prelude ()
> import Booleans
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import LeftFold
> import Snoc

Today we'll define a function that takes a list and reverses the order of its elements; say, to turn $(a,b,c)$ into $(c,b,a)$ and vice versa.

First we define a utility as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, and define $\varphi : \lists{A} \times A \rightarrow \lists{A}$ by $\varphi(x,a) = \cons(a,x)$. We now define a map $\revcat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ by $$\revcat = \foldl{\varphi}.$$

In Haskell:

> revcat :: (List t) => t a -> t a -> t a
> revcat = foldl phi
>   where
>     phi x a = cons a x

</p></div>
</div>

Since $\revcat$ is defined as a $\foldl{\ast}$, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. Then $\revcat$ is the unique solution $f : \lists{A} \times \lists{A} \rightarrow \lists{A}$ to the following system of equations for all $a \in A$ and $x,y \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(x,\nil) = x \\
 f(x,\cons(a,y)) = f(\cons(a,x),y)
\end{array}\right.$$
</p></div>

<div class="test"><p>

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

</p></div>
</div>

Now $\revcat$ interacts with $\snoc$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have the following.

1. $\revcat(\snoc(a,x),y) = \snoc(a,\revcat(x,y))$.
2. $\revcat(x,\snoc(a,y)) = \cons(a,\revcat(x,y))$.
</p></div>

<div class="proof"><p>
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
 & = & \snoc(a,\revcat(x,\const(b,y))
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
</p></div>

<div class="test"><p>

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

</p></div>
</div>

And we define list reversal in terms of $\revcat$.

<div class="result">
<div class="dfn"><p>
Let $A$ be a set. We define $\rev : \lists{A} \rightarrow \lists{A}$ by $$\rev(x) = \revcat(\nil,x).$$

In Haskell:

> rev :: (List t) => t a -> t a
> rev = revcat nil

</p></div>
</div>

Now $\rev$ is essentially defined here as a left fold, but it can also be characterized as a right fold.

<div class="result">
<div class="thm"><p>
We have $$\rev(x) = \foldr{\nil}{\snoc}(x).$$
</p></div>

<div class="proof"><p>
Let $\varphi$ be as defined in the definition of $\rev$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\snoc}(\nil) \\
 & = & \nil \\
 & = & \revcat(\nil,\nil) \\
 & = & \rev(\nil).
\end{eqnarray*}$$
For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\snoc}(\cons(a,x)) \\
 & = & \snoc(a,\foldr{\nil}{\snoc}(x)) \\
 & = & \snoc(a,\rev(x)) \\
 & = & \snoc(a,\revcat(\nil,x)) \\
 & = & \revcat(\snoc(a,\nil),x) \\
 & = & \revcat(\cons(a,\nil),x) \\
 & = & \revcat(\nil,\cons(a,x)) \\
 & = & \rev(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_rev_foldr :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_rev_foldr _ =
>   testName "rev(x) == foldr(nil,snoc)(x)" $
>   \x -> eq (rev x) (foldr nil snoc x)

</p></div>
</div>

Because $\rev$ is equivalent to a $\foldr{\ast}{\ast}$, it can be characterized as the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. Then $\rev$ is the unique function $f : \lists{A} \rightarrow \lists{A}$ having the property that for all $a \in A$ and $x \in \lists{A}$ we have
$$\left\{\begin{array}{l}
 f(\nil) = \nil \\
 f(\cons(a,x)) = \snoc(a,f(x)).
\end{array}\right.$$
</p></div>

<div class="test"><p>

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

</p></div>
</div>

Special cases:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $a,b \in A$ we have the following.

1. $\rev(\cons(a,\nil)) = \cons(a,\nil)$.
2. $\rev(\cons(a,\cons(b,\nil))) = \cons(b,\cons(a,\nil))$.
</p></div>

<div class="proof"><p>
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
</p></div>

<div class="test"><p>

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

</p></div>
</div>

Now $\rev$ and $\snoc$ interact:

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. Then for all $a \in A$ and $x \in \lists{A}$, we have $$\rev(\snoc(a,x)) = \cons(a,\rev(x)).$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \rev(\snoc(a,\nil)) \\
 & = & \revcat(\nil,\snoc(a,x)) \\
 & = & \cons(a,\revcat(\nil,x)) \\
 & = & \cons(a,\rev(x))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_rev_snoc :: (List t, Equal (t a))
>   => t a -> Test (a -> a -> t a -> Bool)
> _test_rev_snoc _ =
>   testName "rev(snoc(a,x)) == cons(a,rev(x))" $
>   \a b x -> eq (rev (snoc a x)) (cons a (rev x))

</p></div>
</div>

And $\rev$ is an involution.

<div class="result">
<div class="lemma"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $\rev(\rev(x)) = x$.
</p></div>

<div class="proof"><p>
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
</p></div>

<div class="test"><p>

> _test_rev_involution :: (List t, Equal (t a))
>   => t a -> Test (t a -> Bool)
> _test_rev_involution _ =
>   testName "rev(rev(x)) == x" $
>   \x -> eq (rev (rev x)) x

</p></div>
</div>

$\rev$ preserves $\isnil$ and $\beq$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x,y \in \lists{A}$. Then we have the following.

1. $\isnil(x) = \isnil(\rev(x))$.
2. $\beq(x,y) = \beq(\rev(x),\rev(y))$.
</p></div>

<div class="proof"><p>
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
</p></div>

<div class="test"><p>

> _test_rev_isnil :: (List t, Equal (t a), Equal a)
>   => t a -> Test (t a -> Bool)
> _test_rev_isnil _ =
>   testName "isnil(rev(x)) == isnil(x)" $
>   \x -> eq (isNil (rev x)) (isNil x)
> 
> 
> _test_rev_eq :: (List t, Equal (t a), Equal a)
>   => t a -> Test (t a -> t a -> Bool)
> _test_rev_eq _ =
>   testName "eq(rev(x),rev(y)) == eq(x,y)" $
>   \x y -> eq (eq (rev x) (rev y)) (eq x y)

</p></div>
</div>

And left fold is a reversed right fold.

<div class="result">
<div class="thm"><p>
Let $\varphi : B \times A \rightarrow B$, and define $\psi : A \times B \rightarrow B$ by $$\psi(a,b) = \varphi(b,a).$$ Now $$\foldl{\varphi}(e,x) = \foldr{e,\psi}(\rev(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \foldl{\varphi}(e,\nil) \\
 & = & e \\
 & = & \foldr{e,\psi}(\nil) \\
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
</p></div>

<div class="test"><p>

> _test_rev_foldl :: (List t, Equal (t a), Equal a)
>   => t a -> Test ((a -> a -> a) -> a -> t a -> Bool)
> _test_rev_foldl _ =
>   testName "foldl(phi)(e,x) == foldr(e,flip(phi))(rev(x))" $
>   \phi e x ->
>     let psi a b = phi b a in
>     eq (foldl phi e x) (foldr e psi (rev x))

</p></div>
</div>


Testing
-------

Suite:

> _test_rev ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a)
>   ) => t a -> Int -> Int -> IO ()
> _test_rev t maxSize numCases = do
>   testLabel ("rev: " ++ typeName t)
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
>   runTest args (_test_rev_eq t)
>   runTest args (_test_rev_foldl t)

Main:

> main_rev :: IO ()
> main_rev = do
>   _test_rev (nil :: ConsList Bool)  20 100
>   _test_rev (nil :: ConsList Unary) 20 100
