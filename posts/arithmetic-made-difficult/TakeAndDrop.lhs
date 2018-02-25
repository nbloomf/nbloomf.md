---
title: Take and Drop
author: nbloomf
date: 2017-05-29
tags: arithmetic-made-difficult, literate-haskell
slug: take-drop
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module TakeAndDrop
>   ( take, drop, _test_take_drop, main_take_drop
>   ) where
> 
> import Testing
> import Functions
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers
> import BailoutRecursion
> import MaxAndMin
> import Lists
> import HeadAndTail
> import Cat
> import Length
> import UnfoldN
> import Range
> import Zip
> import PrefixAndSuffix
> import Sublist

Today we'll define two functions, $\take$ and $\drop$, that split a list at a given index. For example, $\take(3)(x)$ should return a list consisting of the first 3 items of $x$. The biggest question to think about is what $\take$ should do if $x$ doesn't have 3 items to take -- should $\take(3)(-)$ mean take *exactly* 3 or take *at most* 3? The simplest interpretation is *at most*, since with *exactly* we'd need the return type to encode a failure case. That said, under the *at most* interpretation, the signature of $\take$ will be $$\take : \nats \rightarrow {\lists{A}}^{\lists{A}}.$$ Usually we'd try to define such a function with a fold, but in this case $\unfoldN(\ast)$ does exactly what we want.

Essentially, $\take$ and $\drop$ compute a kind of "$\cat$-factorization" of a list based on index from the left. This is not the only useful such factorization; we will address two others in future posts.

:::::: definition ::
Let $A$ be a set. Define $f : \lists{A} \rightarrow 1 + \lists{A} \times A$ by
$$f(x) = \left\{ \begin{array}{ll}
 \lft(\ast) & \mathrm{if}\ x = \nil \\
 \rgt((b,a)) & \mathrm{if}\ x = \cons(a,b).
\end{array}\right.$$
We then define $$\take : \nats \rightarrow {\lists{A}}^{\lists{A}}$$ by $$\take(k)(x) = \unfoldN(f)(k,x).$$

In Haskell:

> take :: (Natural n, List t) => n -> t a -> t a
> take = unfoldN f
>   where
>     f z = case uncons z of
>       Left () -> Left ()
>       Right (Pair a u) -> Right (tup u a)

::::::::::::::::::::

Since $\take$ is defined as an $\unfoldN(\ast)$, it can be characterized as the unique solution to a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\take$ is the unique map $f : \nats \rightarrow {\lists{A}}^{\lists{A}}$ satisfying the following equations for all $n \in \nats$, $a \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\zero,x) = \nil \\
 f(\next(n),\nil) = \nil \\
 f(\next(n),\cons(a,x)) = \cons(a,f(n,x))
\end{array}\right.$$

::: test :::::::::::

> _test_take_zero :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_take_zero _ n =
>   testName "take(zero,x) == nil" $
>   \x -> eq (take (zero `withTypeOf` n) x) nil
> 
> 
> _test_take_next_nil :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> Bool)
> _test_take_next_nil t _ =
>   testName "take(next(n),nil) == nil" $
>   \n -> eq (take (next n) (nil `withTypeOf` t)) nil
> 
> 
> _test_take_next_cons :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_take_next_cons _ _ =
>   testName "take(next(n),cons(a,x)) == cons(a,take(n,x))" $
>   \n a x -> eq
>     (take (next n) (cons a x))
>     (cons a (take n x))

::::::::::::::::::::
::::::::::::::::::::

$\take(n)$ is a prefix.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\prefix(\take(k,x),x) = \btrue.$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \prefix(\take(k,x),x) \\
 & = & \prefix(\take(\zero,x),x) \\
 & = & \prefix(\nil,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for all $x$ for some $k$. We now proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\take(\next(k),\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \prefix(\take(\next(k),\cons(a,x)),\cons(a,x)) \\
 & = & \prefix(\cons(a,\take(k,x)),\cons(a,x)) \\
 & = & \prefix(\take(k,x),x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_prefix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_prefix _ _ =
>   testName "prefix(take(k,x),x) == true" $
>   \k x -> prefix (take k x) x

::::::::::::::::::::
::::::::::::::::::::

$\take(n)$ gives a sublist.

:::::: theorem :::::
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\sublist(\take(k,x),x) = \btrue.$$

::: proof ::::::::::
We have $$\prefix(\take(k,x),x) = \btrue,$$ so $$\infix(\take(k,x),x) = \btrue,$$ so $$\sublist(\take(k,x),x) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_sublist :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_sublist _ _ =
>   testName "sublist(take(k,x),x) == true" $
>   \k x -> sublist (take k x) x

::::::::::::::::::::
::::::::::::::::::::

$\take$ has bounded length:

:::::: theorem :::::
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\length(\take(k,x)) = \nmin(k,\length(x)).$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\take(k,x)) \\
 & = & \length(\take(\zero,x)) \\
 & = & \length(\nil) \\
 &     \href{@length@#cor-length-nil}
   = & \zero \\
 &     \href{@max-min@#thm-min-zero-left}
   = & \nmin(\zero,\length(x)) \\
 & = & \nmin(k,\length(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We now proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\take(\next(k),x)) \\
 & = & \length(\take(\next(k),\nil)) \\
 & = & \length(\nil) \\
 &     \href{@length@#cor-length-nil}
   = & \zero \\
 & = & \nmin(\next(k),\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \nmin(\next(k),\length(\nil)) \\
 & = & \nmin(\next(k),\length(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \length(\take(\next(k),\cons(a,x))) \\
 & = & \length(\cons(a,\take(k,x))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\take(k,x))) \\
 & = & \next(\nmin(k,\length(x))) \\
 &     \href{@max-min@#thm-next-min-distribute}
   = & \nmin(\next(k),\next(\length(x))) \\
 & = & \nmin(\next(k),\length(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_length _ _ =
>   testName "length(take(k,x)) == min(k,length(x))" $
>   \k x -> eq (length (take k x)) (min k (length x))

::::::::::::::::::::
::::::::::::::::::::

$\take$ "distributes over" $\zip$.

:::::: theorem :::::
Let $A$ and $B$ be sets with $x \in \lists{A}$, $y \in \lists{B}$, and $k \in \nats$. Then $$\zip(\take(k,x),\take(k,y)) = \take(k,\zip(x,y)).$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(k,x),\take(k,y)) \\
 & = & \zip(\take(\zero,x),\take(\zero,y)) \\
 & = & \zip(\nil,\nil) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil \\
 & = & \take(\zero,\zip(x,y)) \\
 & = & \take(k,\zip(x,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ and $y$ for some $k$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),\nil),\take(\next(k),y)) \\
 & = & \zip(\nil,\take(\next(k),y)) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \nil \\
 & = & \take(\next(k),\nil) \\
 &     \href{@zip@#cor-zip-nil-left}
   = & \take(\next(k),\zip(\nil,y)) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,u)$ for some $u$. We now consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),x),\take(\next(k),\nil)) \\
 & = & \zip(\take(\next(k),x),\nil) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \nil \\
 & = & \take(\next(k),\nil) \\
 &     \href{@zip@#thm-zip-nil-right}
   = & \take(\next(k),\zip(x,\nil)) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed. Suppose instead that $y = \cons(b,v)$. Now
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),\cons(a,u)),\take(\next(k),\cons(b,v))) \\
 & = & \cons((a,b),\zip(\take(k,u),\take(k,v))) \\
 & = & \cons((a,b),\take(k,\zip(u,v))) \\
 & = & \take(\next(k),\cons((a,b),\zip(u,v))) \\
 & = & \take(\next(k),\zip(\cons(a,u),\cons(b,v))) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_zip :: (List t, Natural n, Equal (t (Pair a b)))
>   => t a -> t b -> n -> Test (n -> t a -> t b -> Bool)
> _test_take_zip _ _ _ =
>   testName "zip(take(n)(x),take(n)(y)) == take(n)(zip(x,y))" $
>   \k x y -> eq
>     (zip (take k x) (take k y))
>     (take k (zip x y))

::::::::::::::::::::
::::::::::::::::::::

$\take$ interacts with $\range$.

:::::: theorem :::::
For all $a,b,k \in \nats$, we have $$\take(k,\range(a,b)) = \range(a,\nmin(k,b)).$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(k,\range(a,b)) \\
 & = & \take(\zero,\range(a,b)) \\
 & = & \nil \\
 & = & \range(a,\zero) \\
 &     \href{@max-min@#thm-min-zero-left}
   = & \range(a,\nmin(\zero,b)) \\
 & = & \range(a,\nmin(k,b))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $b$ for some $k$. We consider two possibilities for $b$. If $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\range(a,b)) \\
 & = & \take(\next(k),\range(a,\zero)) \\
 & = & \take(\next(k),\nil) \\
 & = & \nil \\
 & = & \range(a,\zero) \\
 & = & \range(a,\nmin(\next(k),\zero)) \\
 & = & \range(a,\nmin(\next(k),b))
\end{eqnarray*}$$
as needed. If $b = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\range(a,b)) \\
 & = & \take(\next(k),\range(a,\next(m))) \\
 & = & \take(\next(k),\cons(a,\range(\next(a),m))) \\
 & = & \cons(a,\take(k,\range(\next(a),m))) \\
 & = & \cons(a,\range(\next(a),\nmin(k,m))) \\
 & = & \range(a,\next(\nmin(k,m))) \\
 &     \href{@max-min@#thm-next-min-distribute}
   = & \range(a,\nmin(\next(k),\next(m))) \\
 & = & \range(a,\nmin(\next(k),b))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_range :: (List t, Equal a, Natural n, Equal n, Equal (t n))
>   => t a -> n -> Test (n -> n -> n -> t n -> Bool)
> _test_take_range _ _ =
>   testName "take(n)(range(a,b)) == range(a,min(n,b))" $
>   \n a b t -> eq
>     (take n ((range a b) `withTypeOf` t))
>     (range a (min n b))

::::::::::::::::::::
::::::::::::::::::::

$\take$ is idempotent.

:::::: theorem :::::
Let $A$ be a set. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\take(k,\take(k,x)) = \take(k,x).$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(k,\take(k,x)) \\
 & = & \take(\zero,\take(k,x)) \\
 & = & \nil \\
 & = & \take(\zero,x) \\
 & = & \take(k,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We now consider two possibilities. If $x = \nil$, then
$$\begin{eqnarray*}
 &   & \take(\next(k),\take(\next(k),x)) \\
 & = & \take(\next(k),\take(\next(k),\nil)) \\
 & = & \take(\next(k),\nil) \\
 & = & \take(\next(k),x)
\end{eqnarray*}$$
as needed. If $x = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\take(\next(k),x)) \\
 & = & \take(\next(k),\take(\next(k),\cons(a,u))) \\
 & = & \take(\next(k),\cons(a,\take(k,u))) \\
 & = & \cons(a,\take(k,\take(k,u))) \\
 & = & \cons(a,\take(k,u)) \\
 & = & \take(\next(k),\cons(a,u)) \\
 & = & \take(\next(k),x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_idempotent :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_idempotent _ _ =
>   testName "take(k,(take(k,x))) == take(k,take(k,x))" $
>   \k x -> eq (take k (take k x)) (take k x)

::::::::::::::::::::
::::::::::::::::::::

Now for $\drop$. For this function, $\unfoldN$ doesn't have quite the right shape; fundamentally $\unfoldN$ "builds up" a list from the iterated images of a function, but $\drop$ needs to "tear down" a list, with it's natural number argument acting as a countdown. One of our other $\nats$ recursion operators will work for this -- we'll use bailout recursion for efficiency.

:::::: definition ::
Let $A$ be a set. Define $\beta : \nats \times A \rightarrow \bool$ by $$\beta(m,x) = \isnil(x),$$ $\psi : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\psi(m,x) = x,$$ and $\omega : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\omega(k,x) = \tail(x).$$ We then define $\drop : \nats \rightarrow {\lists{A}}^{\lists{A}}$ by $$\drop(k)(x) = \bailrec(\id)(\beta)(\psi)(\omega)(k,x).$$

In Haskell:

> drop :: (Natural n, List t) => n -> t a -> t a
> drop = bailoutRec id beta psi omega
>   where
>     beta  _ x = isNil x
>     psi   _ x = x
>     omega _ x = tail x

::::::::::::::::::::

Since $\drop$ is defined in terms of bailout recursion, it can be characterized as the unique solution of a system of functional equations.

:::::: corollary :::
Let $A$ be a set. $\drop$ is the unique map $f : \nats \rightarrow {\lists{A}}^{\lists{A}}$ satisfying the following equations for all $k \in \nats$, $a \in A$, and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\zero,x) = x \\
 f(\next(n),\nil) = \nil \\
 f(\next(n),\cons(a,x)) = f(n,x)
\end{array}\right.$$

::: test :::::::::::

> _test_drop_zero :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_drop_zero _ n =
>   testName "drop(zero,x) == x" $
>   \x -> eq (drop (zero `withTypeOf` n) x) x
> 
> 
> _test_drop_next_nil :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> Bool)
> _test_drop_next_nil t _ =
>   testName "drop(next(n),nil) == nil" $
>   \n -> eq (drop (next n) (nil `withTypeOf` t)) nil
> 
> 
> _test_drop_next_cons :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> a -> t a -> Bool)
> _test_drop_next_cons _ _ =
>   testName "drop(next(n),cons(a,x)) == cons(a,drop(n,x))" $
>   \n a x -> eq
>     (drop (next n) (cons a x))
>     (drop n x)

::::::::::::::::::::
::::::::::::::::::::

$\drop$ gives a $\suffix$.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\suffix(\drop(k,x),x) = \btrue.$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(k,x),x) \\
 & = & \suffix(\drop(\zero,x),x) \\
 & = & \suffix(x,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(\next(k),x),x) \\
 & = & \suffix(\drop(\next(k),\nil),\nil) \\
 & = & \suffix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. By the inductive hypothesis, we have $$\suffix(\drop(k,x),x) = \btrue$$ and note also that $$\suffix(x,\cons(a,x)) = \btrue.$$ Since $\suffix$ is transitive, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(\next(k),\cons(a,x)),\cons(a,x)) \\
 & = & \suffix(\drop(k,x),\cons(a,x)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_drop_suffix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_drop_suffix _ _ =
>   testName "suffix(drop(k,x),x) == true" $
>   \k x -> eq (suffix (drop k x) x) true

::::::::::::::::::::
::::::::::::::::::::

$\take$ and $\drop$ give a kind of $\cat$-factorization.

:::::: theorem :::::
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$x = \cat(\take(k,x),\drop(k,x)).$$

::: proof ::::::::::
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \cat(\take(k,x),\drop(k,x)) \\
 & = & \cat(\take(\zero,x),\drop(\zero,x)) \\
 & = & \cat(\nil,x) \\
 &     \href{@cat@#cor-cat-nil}
   = & x
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \cat(\take(\next(k),x),\drop(\next(k),x)) \\
 & = & \cat(\take(\next(k),\nil),\drop(\next(k),\nil)) \\
 & = & \cat(\nil,\nil) \\
 &     \href{@cat@#cor-cat-nil}
   = & \nil \\
 & = & x
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \cat(\take(\next(k),\cons(a,x)),\drop(\next(k),\cons(a,x))) \\
 & = & \cat(\cons(a,\take(k,x)),\drop(k,x)) \\
 &     \href{@cat@#cor-cat-cons}
   = & \cons(a,\cat(\take(k,x),\drop(k,x))) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_take_drop_cat :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_drop_cat _ _ =
>   testName "cat(take(k,x),drop(k,x)) == x" $
>   \k x -> eq (cat (take k x) (drop k x)) x

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_take_drop ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   , Equal (t b), Show (t b), Arbitrary (t b), Equal (t (Pair a b))
>   , Arbitrary (t n), Show (t n), Equal (t n)
>   ) => t a -> t b -> n -> Int -> Int -> IO ()
> _test_take_drop t u k size cases = do
>   testLabel1 "take & drop" t
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_take_zero t k)
>   runTest args (_test_take_next_nil t k)
>   runTest args (_test_take_next_cons t k)
>   runTest args (_test_take_prefix t k)
>   runTest args (_test_take_sublist t k)
>   runTest args (_test_take_length t k)
>   runTest args (_test_take_zip t u k)
>   runTest args (_test_take_range t k)
>   runTest args (_test_take_idempotent t k)
> 
>   runTest args (_test_drop_zero t k)
>   runTest args (_test_drop_next_nil t k)
>   runTest args (_test_drop_next_cons t k)
>   runTest args (_test_drop_suffix t k)
> 
>   runTest args (_test_take_drop_cat t k)

Main:

> main_take_drop :: IO ()
> main_take_drop = do
>   _test_take_drop (nil :: ConsList Bool)  (nil :: ConsList Bool)  (zero :: Unary) 50 200
>   _test_take_drop (nil :: ConsList Unary) (nil :: ConsList Unary) (zero :: Unary) 50 200
>   _test_take_drop (nil :: ConsList Bool)  (nil :: ConsList Unary) (zero :: Unary) 50 200
>   _test_take_drop (nil :: ConsList Unary) (nil :: ConsList Bool)  (zero :: Unary) 50 200
