---
title: Select
author: nbloomf
date: 2017-05-25
tags: arithmetic-made-difficult, literate-haskell
slug: select
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Select
>   ( select, _test_select, main_select
>   ) where
> 
> import Testing
> import Booleans
> import NaturalNumbers
> import Choose
> import Lists
> import DoubleBailoutFold
> import Cat
> import Length
> import Map
> import AllAndAny
> import Sublist

Today we'll define a function, $\select$, which takes a natural number $n$ and a list $x$ and constructs the list of all length $n$ sublists of $x$. The signature of $\select$ should be $$\nats \times \lists{A} \rightarrow \lists{\lists{A}},$$ which matches several of our recursion operators. After trying a few, we'll use double bailout fold.

:::::: definition ::
Let $A$ be a set. Define $\delta : \nats \rightarrow \lists{\lists{A}}$ by $$\delta(n) = \bif{\iszero(n)}{\cons(\nil,\nil)}{\nil},$$ $\beta : A \times \lists{A} \times \nats \rightarrow \bool$ by $$\beta(a,x,n) = \iszero(n),$$ $\psi : A \times \lists{A} \times \nats \rightarrow \lists{\lists{A}}$ by $$\psi(a,x,n) = \cons(\nil,\nil),$$ and $\chi : A \times \lists{A} \times \nats \times \lists{\lists{A}} \times \lists{\lists{A}} \rightarrow \lists{\lists{A}}$ by $$\chi(a,x,n,u,v) = \cat(\map(\cons(a,-))(v),u).$$ Now define $\select : \nats \times \lists{A} \rightarrow \lists{\lists{A}}$ by $$\select(n,x) = \dbfoldr{\delta}{\beta}{\prev}{\psi}{\chi}(x,n).$$

In Haskell:

> select :: (List t, Natural n) => n -> t a -> t (t a)
> select n x = dbfoldr delta beta prev psi chi x n
>   where
>     delta m = if isZero m then cons nil nil else nil
>     beta _ _ m = isZero m
>     psi _ _ _ = cons nil nil
>     chi a _ _ u v = cat (map (cons a) v) u

::::::::::::::::::::

Since $\select$ is defined as a double bailout fold, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\select$ is the unique map $f : \nats \times \lists{A} \rightarrow \lists{\lists{A}}$ satisfying the following equations for all $n \in \nats$, $a \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(n,\nil) = \bif{\iszero(n)}{\cons(\nil,\nil)}{\nil} \\
 f(n,\cons(a,x)) = \bif{\iszero(n)}{\cons(\nil,\nil)}{\cat(\map(\cons(a,-))(f(\prev(n),x)),f(n,x))}
\end{array}\right.$$

In particular, we have $$\select(\zero,\cons(a,x)) = \cons(\nil,\nil)$$ and $$\select(\next(n),\cons(a,x)) = \cat(\map(\cons(a,-))(\select(n,x)),\select(\next(n),x)).$$

::: test :::::::::::

> _test_select_nil :: (List t, Equal a, Natural n, Equal n, Equal (t (t a)))
>   => t a -> n -> Test (n -> Bool)
> _test_select_nil t _ =
>   testName "select(n,nil) == if(eq(n,zero),cons(nil,nil),nil)" $
>   \n -> eq
>     (select n (nil `withTypeOf` t))
>     (if isZero n then cons nil nil else nil)
> 
> 
> _test_select_cons :: (List t, Equal a, Natural n, Equal n, Equal (t (t a)))
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_select_cons _ _ =
>   testName "select(n,cons(a,x)) == if(eq(n,zero),cons(nil,nil),cat(map(cons(a,-))(select(prev(n),x)),select(n,x)))" $
>   \n a x -> eq
>     (select n (cons a x))
>     (if isZero n then cons nil nil else cat (map (cons a) (select (prev n) x)) (select n x))

::::::::::::::::::::
::::::::::::::::::::

We can directly compute $\select(\zero,-)$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\select(\zero,x) = \cons(\nil,\nil).$$

::: proof ::::::::::
If $x = \nil$, then
$$\begin{eqnarray*}
 &   & \select(\zero,\nil) \\
 & = & \bif{\iszero(\zero)}{\cons(\nil,\nil)}{\nil} \\
 & = & \cons(\nil,\nil),
\end{eqnarray*}$$
and if $x = \cons(a,u)$, then
$$\begin{eqnarray*}
 &   & \select(\zero,\cons(a,u)) \\
 & = & \bif{\iszero(\zero)}{\cons(\nil,\nil)}{\cat(\map(\cons(a,-))(\select(\prev(\zero),u)),\select(\zero,u))} \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_zero :: (List t, Equal a, Natural n, Equal n, Equal (t (t a)))
>   => t a -> n -> Test (t a -> Bool)
> _test_select_zero _ n =
>   testName "select(zero,x) == cons(nil,nil)" $
>   \x -> eq (select (zero `withTypeOf` n) x) (cons nil nil)

::::::::::::::::::::
::::::::::::::::::::

We can directly compute $\select(\next(\zero),-)$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\select(\next(\zero),x) = \map(\cons(-,\nil))(x).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \select(\next(\zero),x) \\
 & = & \select(\next(\zero),\nil) \\
 & = & \bif{\isnil(\next(\zero))}{\cons(\nil,\nil)}{\nil} \\
 & = & \nil \\
 & = & \map(\cons(-,\nil))(\nil) \\
 & = & \map(\cons(-,\nil))(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \select(\next(\zero),\cons(a,x)) \\
 & = & \cat(\map(\cons(a,-))(\select(\zero,x)),\select(\next(\zero),x)) \\
 & = & \cat(\map(\cons(a,-))(\cons(\nil,\nil)),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\cons(\cons(a,\nil),\map(\cons(a,-))(\nil)),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\cons(\cons(a,\nil),\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\snoc(\cons(a,\nil),\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\nil,\cons(\cons(a,\nil),\map(\cons(-,\nil))(x))) \\
 & = & \cons(\cons(a,\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cons(\cons(-,\nil)(a),\map(\cons(-,\nil))(x)) \\
 & = & \map(\cons(-,\nil))(\cons(a,x))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_one :: (List t, Equal a, Natural n, Equal n, Equal (t (t a)))
>   => t a -> n -> Test (t a -> Bool)
> _test_select_one _ n =
>   testName "select(next(zero),x) == map(cons(-,nil))(x)" $
>   \x -> eq
>     (select ((next zero) `withTypeOf` n) x)
>     (map (\a -> cons a nil) x)

::::::::::::::::::::
::::::::::::::::::::

$\select$ interacts with $\length$.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$. For all $k \in \nats$, we have $$\length(\select(k,x)) = \nchoose(\length(x),k).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\select(k,x)) \\
 & = & \length(\select(k,\nil)) \\
 & = & \length(\bif{\iszero(k)}{\cons(\nil,\nil)}{\nil}) \\
 &     \href{@booleans@#thm-iffunc}
   = & \bif{\iszero(k)}{\length(\cons(\nil,\nil))}{\length(\nil)} \\
 & = & \bif{\iszero(k)}{\next(\zero)}{\zero} \\
 & = & \nchoose(\zero,k) \\
 &     \href{@length@#cor-length-nil}
   = & \nchoose(\length(\nil),k) \\
 & = & \nchoose(\length(x),k)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\select(k,\cons(a,x))) \\
 & = & \length(\select(\zero,\cons(a,x))) \\
 & = & \length(\cons(\nil,\nil)) \\
 &     \href{@length@#thm-length-singleton}
   = & \next(\zero) \\
 & = & \nchoose(\next(\length(x)),\zero) \\
 & = & \nchoose(\length(\cons(a,x)),k)
\end{eqnarray*}$$
as needed. If $k = \next(m)$, then using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \length(\select(k,\cons(a,x))) \\
 & = & \length(\select(\next(m),\cons(a,x))) \\
 & = & \length(\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \nplus(\length(\map(\cons(a,-))(\select(m,x))),\length(\select(\next(m),x))) \\
 & = & \nplus(\length(\select(m,x)),\length(\select(\next(m),x))) \\
 & = & \nplus(\nchoose(\length(x),m),\nchoose(\length(x),\next(m))) \\
 &     \href{@plus@#thm-plus-commutative}
   = & \nplus(\nchoose(\length(x),\next(m)),\nchoose(\length(x),m)) \\
 & = & \nchoose(\next(\length(x)),\next(m)) \\
 & = & \nchoose(\length(\cons(a,x)),k)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_select_length _ _ =
>   testName "length(select(k,x)) == choose(length(x),k)" $
>   \k x -> eq (length (select k x)) (choose (length x) k)

::::::::::::::::::::
::::::::::::::::::::

$\select$ is compatible with $\sublist$.

:::::: theorem :::::
Let $A$ be a set and let $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$, then $\sublist(\select(k,x),\select(k,y)) = \btrue$ for all $k \in \nats$.

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, suppose $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \sublist(\select(k,x),\select(k,y)) \\
 & = & \sublist(\select(\zero,x),\select(\zero,y)) \\
 & = & \sublist(\cons(\nil,\nil),\cons(\nil,\nil)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $k$. We now proceed by list induction on $y$. For the base case $y = \nil$, suppose $$\btrue = \sublist(x,y) = \sublist(x,\nil);$$ then we must have $x = \nil$. In this case we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),y)) \\
 & = & \sublist(\select(\next(k),\nil),\select(\next(k),\nil)) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for $\next(k)$ and all $x$ for some $y$, and let $b \in A$. Suppose further that $\sublist(x,\cons(b,y)) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\nil),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\nil,\select(\next(k),\cons(b,y))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,u)$. We have two possibilities. If $a \neq b$, then since $$\btrue = \sublist(x,\cons(b,y)) = \sublist(\cons(a,u),\cons(b,y))$$ we have $\btrue = \sublist(\cons(a,u),y) = \sublist(x,y)$. By the inductive hypothesis on $y$ we have $$\sublist(\select(\next(k),x),\select(\next(k),y)) = \btrue.$$ Moreover, note that
$$\begin{eqnarray*}
 &   & \select(\next(k),\cons(b,y)) \\
 & = & \cat(\map(\cons(b,-))(\select(k,y)),\select(\next(k),y))
\end{eqnarray*}$$
so that, in particular, $$\sublist(\select(\next(k),y),\select(\next(k),\cons(b,y))) = \btrue.$$ Since $\sublist$ is transitive, we have $$\sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) = \btrue$$ as needed.

Suppose instead that $a = b$. Then since $$\btrue = \sublist(x,\cons(b,y)) = \sublist(\cons(a,u),\cons(b,y)),$$ in fact we have $\sublist(u,y) = \btrue$. Using the inductive hypothesis on $k$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(u,y) \\
 & = & \sublist(\select(k,u),\select(k,y)) \\
 & = & \sublist(\map(\cons(a,-))(\select(k,u)),\map(\cons(a,-))(\select(k,y))) \\
 & = & \sublist(H,K)
\end{eqnarray*}$$
and similarly using the inductive hypothesis on $y$ we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(u,y) \\
 & = & \sublist(\select(\next(k),u),\select(\next(k),y)) \\
 & = & \sublist(P,Q).
\end{eqnarray*}$$
Now we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\cons(a,u)),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\cons(a,u)),\select(\next(k),\cons(a,y))) \\
 & = & \sublist(\cat(\map(\cons(a,-))(\select(k,u)),\select(\next(k),u)),\cat(\map(\cons(a,-))(\select(k,y)),\select(\next(k),y))) \\
 & = & \sublist(\cat(H,P),\cat(K,Q)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_sublist :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> t a -> Bool)
> _test_select_sublist _ _ =
>   testName "sublist(x,y) == sublist(select(k,x),select(k,y))" $
>   \k x y -> if sublist x y
>     then sublist (select k x) (select k y)
>     else true

::::::::::::::::::::
::::::::::::::::::::

Selections are sublists.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $k \in \nats$. Then $$\all(\sublist(-,x),\select(k,x)) = \btrue.$$

::: proof ::::::::::
We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(k,x)) \\
 & = & \all(\sublist(-,x),\select(\zero,x)) \\
 & = & \all(\sublist(-,x),\cons(\nil,\nil)) \\
 & = & \band(\sublist(\nil,x),\all(\sublist(-,x),\nil)) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as claimed. Suppose instead that $k = \next(m)$; we proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(k,x)) \\
 & = & \all(\sublist(-,\nil),\select(\next(m),\nil)) \\
 & = & \all(\sublist(-,\nil),\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$ and let $a \in A$. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\map(\cons(a,-))(\select(m,x))) \\
 & = & \all(\sublist(-,\cons(a,x)) \circ \cons(a,-),\select(m,x)) \\
 & = & \all(\sublist(\cons(a,-),\cons(a,x)),\select(m,x)) \\
 & = & \all(\sublist(-,x),\select(m,x)) \\
 & = & \btrue.
\end{eqnarray*}$$
Also using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(\next(m),x)) \\
 & = & \btrue,
\end{eqnarray*}$$
and for all $u \in \lists{A}$, if $\sublist(u,x) = \btrue$ then $\sublist(u,\cons(a,x)) = \btrue$. Thus we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\select(\next(m),x)) \\
 & = & \btrue.
\end{eqnarray*}$$
 Now
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\select(k,\cons(a,x))) \\
 & = & \all(\sublist(-,\cons(a,x)),\select(\next(m),\cons(a,x))) \\
 & = & \all(\sublist(-,\cons(a,x)),\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \band(\all(\sublist(-,\cons(a,x)),\map(\cons(a,-))(\select(m,x))),\all(\sublist(-,\cons(a,x)),\select(\next(m),x))) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_all_sublist :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_select_all_sublist _ _ =
>   testName "all(sublist(-,x),select(k,x))" $
>   \k x -> all (\u -> sublist u x) (select k x)

::::::::::::::::::::
::::::::::::::::::::

Selections have fixed length.

:::::: theorem :::::
Let $A$ be a set with $x \in \lists{A}$ and $k \in \nats$. Then $$\all(\beq(k,\length(-)),\select(k,x)) = \btrue.$$

::: proof ::::::::::
We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,x)) \\
 & = & \all(\beq(\zero,\length(-)),\select(\zero,x)) \\
 & = & \all(\beq(\zero,\length(-)),\cons(\nil,\nil)) \\
 & = & \band(\beq(\zero,\length(\nil)),\all(\beq(\zero,\length(-)),\nil)) \\
 & = & \band(\beq(\zero,\zero),\btrue) \\
 &     \href{@booleans@#thm-eq-reflexive}
   = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as claimed. Suppose instead that $k = \next(m)$. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,x)) \\
 & = & \all(\beq(k,\length(-)),\select(\next(m),\nil)) \\
 & = & \all(\beq(k,\length(-)),\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$ and let $a \in A$. Using the inductive hypothesis (twice!) we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,\cons(a,x))) \\
 & = & \all(\beq(k,\length(-)),\select(\next(m),\cons(a,x))) \\
 & = & \all(\beq(k,\length(-)),\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\all(\beq(k,\length(-)),\select(\next(m),x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\all(\beq(k,\length(-)),\select(k,x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\btrue) \\
 & = & \band(\all(\beq(k,\length(-) \circ \cons(a,-)),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(k,\length(\cons(a,-))),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(\next(m),\next(\length(-))),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(m,\length(-)),\select(m,x)),\btrue) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_select_all_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_select_all_length _ _ =
>   testName "all(eq(k,length(-)),select(k,x))" $
>   \k x -> all (\u -> eq k (length u)) (select k x)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_select ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , TypeName (t a), List t
>   , Equal (t a), Show (t a), Arbitrary (t a), Equal (t (t a))
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_select t n size cases = do
>   testLabel1 "select" t
> 
>   let
>     args = stdArgs
>       { maxSuccess = cases
>       , maxSize    = size
>       }
> 
>   runTest args (_test_select_nil t n)
>   runTest args (_test_select_cons t n)
>   runTest args (_test_select_zero t n)
>   runTest args (_test_select_one t n)
>   runTest args (_test_select_length t n)
>   runTest args (_test_select_sublist t n)
>   runTest args (_test_select_all_sublist t n)
>   runTest args (_test_select_all_length t n)

Main:

> main_select :: IO ()
> main_select = do
>   _test_select (nil :: ConsList Bool)  (zero :: Unary) 20 30
>   _test_select (nil :: ConsList Unary) (zero :: Unary) 20 30
