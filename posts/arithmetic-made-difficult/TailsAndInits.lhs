---
title: Tails and Inits
author: nbloomf
date: 2017-05-12
tags: arithmetic-made-difficult, literate-haskell
slug: tails-inits
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module TailsAndInits
>   ( tails, inits, _test_tails_inits, main_tails_inits
>   ) where
> 
> import Testing
> import Tuples
> import NaturalNumbers
> import Lists
> import ConsumingFold
> import Snoc
> import Reverse
> import Length
> import Map
> import PrefixAndSuffix
> import LongestCommonPrefix
> import AllAndAny

Today we'll construct the lists of all suffixes ($\tails$) and prefixes ($\inits$) of a list. Starting with $\tails$: this function should have a signature like $$\lists{A} \rightarrow \lists{\lists{A}}.$$

:::::: definition ::
Let $A$ be a set. Let $\gamma = \cons(\nil,\nil)$, and define $\sigma : A \times \lists{A} \times \lists{\lists{A}} \rightarrow \lists{\lists{A}}$ by $$\sigma(a,x,z) = \cons(\cons(a,x),z).$$ Now define $\tails : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\tails = \cfoldr(\gamma)(\sigma).$$

In Haskell:

> tails :: (List t) => t a -> t (t a)
> tails = cfoldr gamma sigma
>   where
>     gamma = cons nil nil
>     sigma a x z = cons (cons a x) z

::::::::::::::::::::

Since $\tails$ is defined as a $\cfoldr(\ast)(\ast)$, it is the unique solution to a system of functional equations.

:::::: corollary :::
[]{#cor-tails-nil}[]{#cor-tails-cons}
Let $A$ be a set. $\tails$ is the unique map $f : \lists{A} \rightarrow \lists{\lists{A}}$ which satisfies the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \cons(\nil,\nil) \\
 f(\cons(a,x)) = \cons(\cons(a,x),f(x))
\end{array}\right.$$

::: test :::::::::::

> _test_tails_nil :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test Bool
> _test_tails_nil t =
>   testName "tails(nil) == cons(nil,nil)" $
>   eq (tails (nil `withTypeOf` t)) (cons nil nil)
> 
> 
> _test_tails_cons :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_tails_cons _ =
>   testName "tails(cons(a,x)) == cons(cons(a,x),tails(x))" $
>   \a x -> eq (tails (cons a x)) (cons (cons a x) (tails x))

::::::::::::::::::::
::::::::::::::::::::

Special cases.

:::::: theorem :::::
[]{#thm-tails-one}[]{#thm-tails-two}
Let $A$ be a sets. For all $a,b \in A$ we have the following.

1. $\tails(\cons(a,\nil)) = \cons(\cons(a,\nil),\cons(\nil,\nil))$.
2. $\tails(\cons(a,\cons(b,\nil))) = \cons(\cons(a,\cons(b,\nil)),\cons(\cons(b,\nil),\cons(\nil,\nil)))$.

::: proof ::::::::::
1. Note that
$$\begin{eqnarray*}
 &   & \tails(\cons(a,\nil)) \\
 &     \href{@tails-inits@#cor-tails-cons}
   = & \cons(\cons(a,\nil),\tails(\nil)) \\
 &     \href{@tails-inits@#cor-tails-nil}
   = & \cons(\cons(a,\nil),\cons(\nil,\nil))
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tails(\cons(a,\cons(b,\nil))) \\
 &     \href{@tails-inits@#cor-tails-cons}
   = & \cons(\cons(a,\cons(b,\nil)),\tails(\cons(b,\nil))) \\
 & = & \cons(\cons(a,\cons(b,\nil)),\cons(\cons(a,\nil),\cons(\nil,\nil)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_single :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> Bool)
> _test_tails_single t =
>   testName "tails(cons(a,nil)) == cons(cons(a,nil),cons(nil,nil))" $
>   \a -> eq
>     (tails (cons a (nil `withTypeOf` t)))
>     (cons (cons a nil) (cons nil nil))
> 
> 
> _test_tails_double :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> a -> Bool)
> _test_tails_double t =
>   testName "tails(cons(a,cons(b,nil))) == cons(cons(a,cons(b,nil)),cons(cons(b,nil),cons(nil,nil)))" $
>   \a b -> eq
>     (tails (cons a (cons b (nil `withTypeOf` t))))
>     (cons (cons a (cons b nil)) (cons (cons b nil) (cons nil nil)))

::::::::::::::::::::
::::::::::::::::::::

$\tails$ interacts with $\map$.

:::::: theorem :::::
[]{#thm-tails-map}
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$ we have $$\tails(\map(f)(x)) = \map(\map(f))(\tails(x)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\nil)) \\
 &     \href{@map@#cor-map-nil}
   = & \tails(\nil) \\
 & = & (@@@) \\
 & = & \nil \\
 &     \href{@map@#cor-map-nil}
   = & \map(\map(f))(\nil) \\
 & = & \map(\map(f))(\tails(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\cons(a,x))) \\
 &     \href{@map@#cor-map-cons}
   = & \tails(\cons(f(a),\map(f)(x))) \\
 & = & \cons(\cons(f(a),\map(f)(x)),\tails(\map(f)(x))) \\
 &     \href{@tails-inits@#thm-tails-map}
   = & \cons(\cons(f(a),\map(f)(x)),\map(\map(f))(\tails(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \cons(\map(f)(\cons(a,x)),\map(\map(f))(\tails(x))) \\
 &     \href{@map@#cor-map-cons}
   = & \map(\map(f))(\cons(\cons(a,x),\tails(x))) \\
 & = & \map(\map(f))(\tails(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_map :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_tails_map _ =
>   testName "tails(map(f)(x)) == map(map(f))(tails(x))" $
>   \f x -> eq (tails (map f x)) (map (map f) (tails x))

::::::::::::::::::::
::::::::::::::::::::

$\tails$ interacts with $\length$.

:::::: theorem :::::
[]{#thm-length-tails}
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\tails(x)) = \next(\length(x)).$$ In particular, $\tails{x} \neq \nil$.

::: proof ::::::::::
We proceed by list induction. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\tails(\nil)) \\
 &     \href{@tails-inits@#cor-tails-nil}
   = & \length(\cons(\nil,\nil)) \\
 &     \href{@length@#thm-length-singleton}
   = & \next(\zero) \\
 &     \href{@length@#cor-length-nil}
   = & \next(\length(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \length(\tails(\cons(a,x))) \\
 &     \href{@tails-inits@#cor-tails-cons}
   = & \length(\cons(\cons(a,x),\tails(x))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\tails(x))) \\
 & = & \next(\next(\length(x))) \\
 &     \href{@length@#cor-length-cons}
   = & \next(\length(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_length
>   :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_tails_length _ n =
>   testName "length(tails(x)) == next(length(x))" $
>   \x -> eq (length (tails x)) (next (length x `withTypeOf` n))

::::::::::::::::::::
::::::::::::::::::::

$\tails$ interacts with $\snoc$.

:::::: theorem :::::
[]{#thm-tails-snoc}
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$ we have $$\tails(\snoc(a,x)) = \snoc(\nil,\map(\snoc(a))(\tails(x))).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \snoc(\nil,\map(\snoc(a))(\tails(x))) \\
 & = & \snoc(\nil,\map(\snoc(a))(\tails(\nil))) \\
 &     \href{@tails-inits@#cor-tails-nil}
   = & \snoc(\nil,\map(\snoc(a))(\cons(\nil,\nil))) \\
 &     \href{@map@#cor-map-cons}
   = & \snoc(\nil,\cons(\snoc(a,\nil),\map(\snoc(a))(\nil))) \\
 &     \href{@map@#cor-map-nil}
   = & \snoc(\nil,\cons(\snoc(a,\nil),\nil)) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \cons(\snoc(a,\nil),\snoc(\nil,\nil)) \\
 & = & \cons(\cons(a,\nil),\cons(\nil,\nil)) \\
 &     \href{@tails-inits@#thm-tails-one}
   = & \tails(\cons(a,\nil)) \\
 &     \href{@snoc@#cor-snoc-nil}
   = & \tails(\snoc(a,\nil)) \\
 & = & \tails(\snoc(a,x))
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \tails(\snoc(a,\cons(b,x))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \tails(\cons(b,\snoc(a,x))) \\
 & = & \cons(\cons(b,\snoc(a,x)),\tails(\snoc(a,x))) \\
 &     \href{@tails-inits@#thm-tails-snoc}
   = & \cons(\cons(b,\snoc(a,x)),\snoc(\nil,\map(\snoc(a))(\tails(x)))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(\nil,\cons(\cons(b,\snoc(a,x)),\map(\snoc(a))(\tails(x)))) \\
 &     \href{@snoc@#cor-snoc-cons}
   = & \snoc(\nil,\cons(\snoc(a,\cons(b,x)),\map(\snoc(a))(\tails(x)))) \\
 &     \href{@map@#cor-map-cons}
   = & \snoc(\nil,\map(\snoc(a))(\cons(\cons(b,x),\tails(x)))) \\
 &     \href{@tails-inits@#cor-tails-cons}
   = & \snoc(\nil,\map(\snoc(a))(\tails(\cons(b,x))))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_snoc :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_tails_snoc _ =
>   testName "tails(snoc(a,x)) == snoc(nil,map(snoc(a,-))(tails(x)))" $
>   \a x -> eq (tails (snoc a x)) (snoc nil (map (snoc a) (tails x)))

::::::::::::::::::::
::::::::::::::::::::

And $\tails(x)$ consists of suffixes.

:::::: theorem :::::
[]{#thm-tails-suffix}
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\all(\flip(\suffix)(x),\tails(x)) = \btrue.$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \all(\suffix(-,x),\tails(x)) \\
 & = & \all(\suffix(-,\nil),\cons(\nil,\nil)) \\
 & = & \band(\suffix(\nil,\nil),\all(\suffix(-,\nil),\nil)) \\
 & = & \band(\btrue,\btrue) \\
 &     \href{@and@#thm-and-eval-true-true}
   = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Note that if $\suffix(u,x) = \btrue$ then $\suffix(u,\cons(a,x)) = \btrue$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \all(\suffix(-,x),\tails(x)) \\
 & = & \all(\suffix(-,\cons(a,x)),\tails(x)) \\
 & = & \band(\btrue,\all(\suffix(-,\cons(a,x)),\tails(x))i) \\
 & = & \band(\suffix(\cons(a,x),\cons(a,x)),\all(\suffix(-,\cons(a,x)),\tails(x))) \\
 & = & \all(\suffix(-,\cons(a,x)),\cons(\cons(a,x),\tails(x))) \\
 & = & \all(\suffix(-,\cons(a,x)),\tails(\cons(a,x)))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_suffix :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (t a -> Bool)
> _test_tails_suffix _ =
>   testName "all(suffix(_,x))(tails(x))" $
>   \x -> all (\y -> suffix y x) (tails x)

::::::::::::::::::::
::::::::::::::::::::

Next we'll define $\inits$ in terms of $\tails$.

:::::: definition ::
Let $A$ be a sets. We define $\inits : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\inits(x) = \rev(\map(\rev)(\tails(\rev(x)))).$$

In Haskell:

> inits :: (List t) => t a -> t (t a)
> inits = rev . map rev . tails . rev

::::::::::::::::::::

And likewise, $\tails$ has an expression in terms of $\inits$.

:::::: theorem :::::
[]{#thm-tails-rev}
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\tails(x) = \map(\rev)(\rev(\inits(\rev(x)))).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \map(\rev) \circ \rev \circ \inits \circ \rev \\
 & = & \map(\rev) \circ \rev \circ \rev \circ \map(\rev) \circ \tails \circ \rev \circ \rev \\
 & = & \map(\rev) \circ \map(\rev) \circ \tails \\
 & = & \compose(\map(\compose(\rev)(\rev)))(\tails) \\
 & = & \compose(\map(\id))(\tails) \\
 & = & \tails
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_inits_tails :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (t a -> Bool)
> _test_inits_tails _ =
>   testName "tails(x) == rev(map(rev)(inits(rev(x))))" $
>   \x -> eq (tails x) (map rev (rev (inits (rev x))))

::::::::::::::::::::
::::::::::::::::::::

$\inits$ interacts with $\cons$.

:::::: theorem :::::
[]{#thm-inits-cons}
Let $A$ be a set. For all $a \in A$ and $x \in \lists{A}$, we have $$\inits(\cons(a,x)) = \cons(\nil,\map(\cons(a))(\inits(x))).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \inits(\cons(a,x)) \\
 & = & \rev(\map(\rev)(\tails(\rev(\cons(a,x))))) \\
 &     \href{@rev@#cor-rev-cons}
   = & \rev(\map(\rev)(\tails(\snoc(a,\rev(x))))) \\
 & = & \rev(\map(\rev)(\snoc(\nil,\map(\snoc(a))(\tails(\rev(a)))))) \\
 &     \href{@map@#thm-map-snoc}
   = & \rev(\snoc(\rev(\nil),\map(\rev)(\map(\snoc(a))(\tails(\rev(a)))))) \\
 &     \href{@rev@#cor-rev-nil}
   = & \rev(\snoc(\nil,\map(\rev)(\map(\snoc(a))(\tails(\rev(a)))))) \\
 & = & \rev(\snoc(\nil,\map(\compose(\rev)(\snoc(a)))(\tails(\rev(a))))) \\
 & = & \rev(\snoc(\nil,\map(\cons(a) \circ \rev)(\tails(\rev(a))))) \\
 & = & \rev(\snoc(\nil,\map(\cons(a))(\map(\rev)(\tails(\rev(a)))))) \\
 &     \href{@rev@#thm-rev-snoc}
   = & \cons(\nil,\rev(\map(\cons(a))(\map(\rev)(\tails(\rev(a)))))) \\
 &     \href{@map@#thm-map-rev}
   = & \cons(\nil,\map(\cons(a))(\rev(\map(\rev)(\tails(\rev(a)))))) \\
 & = & \cons(\nil,\map(\cons(a))(\inits(x)))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_inits_cons :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_inits_cons _ =
>   testName "inits(cons(a,x)) == cons(nil,map(cons(a,-))(inits(x)))" $
>   \a x -> eq (inits (cons a x)) (cons nil (map (cons a) (inits x)))

::::::::::::::::::::
::::::::::::::::::::

$\inits$ interacts with $\map$.

:::::: theorem :::::
[]{#thm-inits-map}
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\inits(\map(f)(x)) = \map(\map(f))(\inits(x)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \inits(\map(f)(x)) \\
 & = & \rev(\map(\rev)(\tails(\rev(\map(f)(x))))) \\
 &     \href{@map@#thm-map-rev}
   = & \rev(\map(\rev)(\tails(\map(f)(\rev(x))))) \\
 & = & \rev(\map(\rev)(\map(\map(f))(\tails(\rev(x))))) \\
 & = & \rev(\map(\compose(\rev)(\map(f)))(\tails(\rev(x)))) \\
 & = & \rev(\map(\compose(\map(f))(\rev))(\tails(\rev(x)))) \\
 & = & \rev(\map(\map(f))(\map(\rev)(\tails(\rev(x))))) \\
 &     \href{@map@#thm-map-rev}
   = & \map(\map(f))(\rev(\map(\rev)(\tails(\rev(x))))) \\
 & = & \map(\map(f))(\inits(x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_inits_map :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_inits_map _ =
>   testName "inits(map(f)(x)) == map(map(f))(inits(x))" $
>   \f x -> eq (inits (map f x)) (map (map f) (inits x))

::::::::::::::::::::
::::::::::::::::::::

$\inits$ interacts with $\length$.

:::::: theorem :::::
[]{#thm-length-inits}
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\length(\inits(x)) = \next(\length(x)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \length(\inits(x)) \\
 & = & \length(\rev(\map(\rev)(\tails(\rev(x))))) \\
 &     \href{@length@#thm-length-rev}
   = & \length(\map(\rev)(\tails(\rev(x)))) \\
 & = & \length(\tails(\rev(x))) \\
 &     \href{@tails-inits@#thm-length-tails}
   = & \next(\length(\rev(x))) \\
 &     \href{@length@#thm-length-rev}
   = & \next(\length(x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_inits_length :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_inits_length _ n =
>   testName "length(inits(x)) == next(length(x))" $
>   \x -> eq (length (inits x)) (next (length x `withTypeOf` n))

::::::::::::::::::::
::::::::::::::::::::

$\inits$ distributes over $\lcp$.

:::::: theorem :::::
[]{#thm-inits-lcp}
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\inits(\lcp(x,y)) = \lcp(\inits(x),\inits(y)).$$

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have two possibilities for $y$. If $y = \nil$ we have
$$\begin{eqnarray*}
 &   & \lcp(\inits(x),\inits(y)) \\
 & = & \lcp(\inits(\nil),\inits(\nil)) \\
 & = & \lcp(\cons(\nil,\nil),\cons(\nil,\nil)) \\
 &     \href{@lcp-lcs@#thm-lcp-idempotent}
   = & \cons(\nil,\nil)
\end{eqnarray*}$$
and if $y = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \lcp(\inits(x),\inits(y)) \\
 & = & \lcp(\inits(\nil),\inits(\cons(a,u))) \\
 & = & \lcp(\cons(\nil,\nil),\cons(\nil,\map(\cons(a,-))(\inits(x)))) \\
 & = & \cons(\nil,\lcp(\nil,\map(\cons(a,-))(\inits(x)))) \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ for some $x$, and let $a \in A$. We have two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \inits(\lcp(\cons(a,x),\nil)) \\
 &     \href{@lcp-lcs@#thm-lcp-commutative}
   = & \inits(\lcp(\nil,\cons(a,x))) \\
 & = & \lcp(\tails(\nil),\tails(\cons(a,x))) \\
 &     \href{@lcp-lcs@#thm-lcp-commutative}
   = & \lcp(\tails(\cons(a,x)),\tails(\nil))
\end{eqnarray*}$$
as needed. Suppose then that $y = \cons(b,u)$. If $b = a$, note that $\cons(a,-)$ is injective, so that
$$\begin{eqnarray*}
 &   & \lcp(\tails(\cons(a,x)),\tails(y)) \\
 & = & \lcp(\tails(\cons(a,x)),\tails(\cons(b,u))) \\
 & = & \lcp(\cons(\nil,\map(\cons(a,-))(\tails(x))),\cons(\nil,\map(\cons(b,-))(\tails(u)))) \\
 & = & \lcp(\cons(\nil,\map(\cons(a,-))(\tails(x))),\cons(\nil,\map(\cons(a,-))(\tails(u)))) \\
 & = & \cons(\nil,\lcp(\map(\cons(a,-))(\tails(x)),\map(\cons(a,-))(\tails(u)))) \\
 & = & \cons(\nil,\map(\cons(a,-))(\lcp(\tails(x),\tails(u)))) \\
 & = & \cons(\nil,\map(\cons(a,-))(\tails(\lcp(x,u)))) \\
 & = & \tails(\cons(a,\lcp(x,u))) \\
 & = & \tails(\lcp(\cons(a,x),\cons(a,u))) \\
 & = & \tails(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \tails(\lcp(\cons(a,x),y))
\end{eqnarray*}$$
as needed. If $b \neq a$, we instead, since $\cons(a,x) \neq \cons(b,x)$ for all $x$, we have
$$\begin{eqnarray*}
 &   & \lcp(\tails(\cons(a,x)),\tails(y)) \\
 & = & \lcp(\tails(\cons(a,x)),\tails(\cons(b,u))) \\
 & = & \lcp(\cons(\nil,\map(\cons(a,-))(\tails(x))),\cons(\nil,\map(\cons(b,-))(\tails(u)))) \\
 & = & \cons(\nil,\lcp(\map(\cons(a,-))(\tails(x)),\map(\cons(b,-))(\tails(u)))) \\
 & = & \cons(\nil,\nil) \\
 &     \href{@tails-inits@#cor-tails-nil}
   = & \tails(\nil) \\
 & = & \tails(\lcp(\cons(a,x),\cons(b,u))) \\
 & = & \tails(\lcp(\cons(a,x),y))
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_inits_lcp :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> Test (t a -> t a -> Bool)
> _test_inits_lcp _ =
>   testName "inits(lcp(x,y)) == lcp(inits(x),inits(y))" $
>   \x y -> eq (inits (lcp x y)) (lcp (inits x) (inits y))

::::::::::::::::::::
::::::::::::::::::::

And $\tails$ distributes over $\lcs$.

:::::: theorem :::::
[]{#thm-tails-lcs}
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\tails(\lcs(x,y)) = \lcs(\tails(x),\tails(y)).$$

::: proof ::::::::::
Note that $\rev$ is injective, so that
$$\begin{eqnarray*}
 &   & \tails(\lcs(x,y)) \\
 &     \href{@tails-inits@#thm-tails-rev}
   = & \map(\rev)(\rev(\inits(\rev(\lcs(x,y))))) \\
 & = & \map(\rev)(\rev(\inits(\lcp(\rev(x),\rev(y))))) \\
 &     \href{@tails-inits@#thm-inits-lcp}
   = & \map(\rev)(\rev(\lcp(\inits(\rev(x)),\inits(\rev(y))))) \\
 &     \href{@map@#thm-map-rev}
   = & \rev(\map(\rev)(\lcp(\inits(\rev(x)),\inits(\rev(y))))) \\
 & = & \rev(\lcp(\map(\rev)(\inits(\rev(x))),\map(\rev)(\inits(\rev(y))))) \\
 & = & \lcs(\rev(\map(\rev)(\inits(\rev(x)))),\rev(\map(\rev)(\inits(\rev(y))))) \\
 & = & \lcs(\tails(x),\tails(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_tails_lcs :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> Test (t a -> t a -> Bool)
> _test_tails_lcs _ =
>   testName "tails(lcs(x,y)) == lcs(tails(x),tails(y))" $
>   \x y -> eq (tails (lcs x y)) (lcs (tails x) (tails y))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_tails_inits ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName n, Natural n, Equal n
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (Pair a a)), Equal (t (t a))
>   ) => Int -> Int -> t a -> n -> IO ()
> _test_tails_inits size cases t n = do
>   testLabel2 "tails & inits" t n
> 
>   let args = testArgs size cases
> 
>   runTest args (_test_tails_nil t)
>   runTest args (_test_tails_cons t)
>   runTest args (_test_tails_single t)
>   runTest args (_test_tails_double t)
>   runTest args (_test_tails_map t)
>   runTest args (_test_tails_length t n)
>   runTest args (_test_tails_snoc t)
>   runTest args (_test_tails_suffix t)
> 
>   runTest args (_test_inits_tails t)
>   runTest args (_test_inits_cons t)
>   runTest args (_test_inits_map t)
>   runTest args (_test_inits_length t n)
> 
>   runTest args (_test_inits_lcp t)
>   runTest args (_test_tails_lcs t)

Main:

> main_tails_inits :: IO ()
> main_tails_inits = do
>   _test_tails_inits 20 100 (nil :: ConsList Bool)  (zero :: Unary)
>   _test_tails_inits 20 100 (nil :: ConsList Unary) (zero :: Unary)
