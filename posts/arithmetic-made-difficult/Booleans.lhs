---
title: Booleans
author: nbloomf
date: 2014-04-01
tags: arithmetic-made-difficult, literate-haskell
slug: booleans
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Booleans
>   ( Boolean, true, false, ifThenElse, isTrue, isFalse
>   , _test_boolean, main_boolean
>   ) where
> 
> import Testing
> import Functions
> import Flip
> import Clone

Before we think about numbers or writing programs, let's start by nailing down some important ideas about truth values. In math there can be a kind of other-worldness about true and false, since they live in the "metalanguage" of mathematical logic rather than the "object language" of whatever we are studying. But it will turn out to be useful to algebraify the truth values themselves.

We're going to characterize the boolean values true and false in a roundabout way. First, we define a kind of algebra.

:::::: definition ::
[]{#def-doubly-pointed-set}
A *doubly-pointed set* is a set $A$ with two (not necessarily distinct) distinguished elements $a_t, a_f \in A$. If $A$ and $B$ are doubly-pointed sets with distinguished elements $a_t, a_f \in A$ and $b_t, b_f \in B$, a map $\theta : A \rightarrow B$ is called a *doubly-pointed homomorphism* if $\theta(a_t) = b_t$ and $\theta(a_f) = b_f$.
::::::::::::::::::::

As algebras go, doubly-pointed sets are almost as weak as they come. We can see shades of the boolean values there -- "true" and "false" can be thought of as distinguished elements  in a doubly-pointed set. And indeed we'll do that. But the booleans are not just any doubly-pointed set; they are the *smallest* such set in a precise sense.

:::::: definition ::
[]{#def-bool}
There is a special doubly-pointed set, denoted $\bool$, with distinguished elements $\btrue$ and $\bfalse$, with the property that if $A$ is a doubly-pointed set with distinguished elements $a_t, a_f$, then there is a *unique* doubly-pointed homomorphism $\Theta : \bool \rightarrow A$. We denote this $\Theta$ by $$\Theta(p) = \bif{p}{a_t}{a_f}.$$
::::::::::::::::::::

What makes the booleans special among doubly-pointed sets is this unique map, which looks suspiciously like the traditional "if-then-else" construct, because that's exactly what it is.

:::::: corollary :::
[]{#cor-if-true}[]{#cor-if-false}
Let $(A,a_t,a_f)$ be a doubly pointed set. Then we have the following.

1. $\bif{\btrue}{a_t}{a_f} = a_t$.
2. $\bif{\bfalse}{a_t}{a_f} = a_f$.

::: test :::::::::::

> _test_if_true :: (Boolean b, Equal a)
>   => b -> a -> Test (a -> a -> Bool)
> _test_if_true p _ =
>   testName "if(true,a,b) == a" $
>   \x y -> eq (ifThenElse (true `withTypeOf` p) x y) x
> 
> 
> _test_if_false :: (Boolean b, Equal a)
>   => b -> a -> Test (a -> a -> Bool)
> _test_if_false p _ =
>   testName "if(false,a,b) == a" $
>   \x y -> eq (ifThenElse (false `withTypeOf` p) x y) y

::::::::::::::::::::
::::::::::::::::::::

This is a weird way to define $\bool$ -- but there's a really good reason for it, which we'll get into later.

I'm referring to "the" booleans as if they are uniquely determined, but of course they aren't -- any other doubly-pointed set that also maps uniquely to any other is indistinguishable from $\bool$ up to a renaming of the special elements. For this reason we'll wrap up the important information about $\bool$ in a type class, rather than a single type.

> class Boolean b where
>   true, false :: b
> 
>   ifThenElse :: b -> a -> a -> a

Of course the Haskell ``Bool`` type is an instance.

> instance Boolean Bool where
>   true = True
>   false = False
> 
>   ifThenElse p x y = if p then x else y

It will be handy later to name these two functions from an abstract boolean set to ``Bool``.

> isTrue :: (Boolean b) => b -> Bool
> isTrue p = ifThenElse p true false
> 
> isFalse :: (Boolean b) => b -> Bool
> isFalse p = ifThenElse p false true

There are many other instances which differ only by the labels of $\btrue$ and $\bfalse$, and depending on the context, a different concrete instance might make more sense. We could call the distinguished elements of $\bool$ "Yes/No", "Present/Absent", or something else, and the essence of booleanness would not change.

$\bif{\ast}{\ast}{\ast}$ enjoys some other nice properties. For instance, $\bif{p}{a}{a} = \btrue$.

:::::: theorem :::::
[]{#thm-if-same}
Let $A$ be a set with $a \in A$. If $p \in \bool$, we have $$\bif{p}{a}{a} = a.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{a} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{a}{a} \\
 &     \href{@booleans@#cor-if-true}
   = & a
\end{eqnarray*}$$
and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{a} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{a}{a} \\
 &     \href{@booleans@#cor-if-false}
   = & a
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_if_same :: (Equal a, Boolean b)
>   => b -> a -> Test (b -> a -> Bool)
> _test_if_same _ _ =
>   testName "if(p,a,a) == a" $
>   \p a -> eq (ifThenElse p a a) a

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ interacts with function application.

:::::: theorem :::::
[]{#thm-iffunc}
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $p \in \bool$ and $u,v \in A$, we have $$f(\bif{p}{u}{v}) = \bif{p}{f(u)}{f(v)}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 &     \let{p = \btrue}
   = & f(\bif{\btrue}{u}{v}) \\
 &     \href{@booleans@#cor-if-true}
   = & f(u) \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{f(u)}{f(v)} \\
 &     \let{p = \btrue}
   = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 &     \let{p = \bfalse}
   = & f(\bif{\bfalse}{u}{v}) \\
 &     \href{@booleans@#cor-if-false}
   = & f(v) \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{f(u)}{f(v)} \\
 &     \let{p = \bfalse}
   = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_func :: (Equal a, Boolean b)
>   => b -> a -> Test ((a -> a) -> b -> a -> a -> Bool)
> _test_if_func _ _ =
>   testName "f(if(p,a,b)) == if(p,f(a),f(b))" $
>   \f p a b -> eq (f (ifThenElse p a b)) (ifThenElse p (f a) (f b))

::::::::::::::::::::
::::::::::::::::::::

Nested $\bif{\ast}{\ast}{\ast}$s commute (sort of).

:::::: theorem :::::
[]{#thm-ifnest}
Let $A$ be a set with $p,q \in \bool$ and $a,b,c,d \in A$. Then we have
$$\begin{eqnarray*}
  &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
  & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}.
\end{eqnarray*}$$

::: proof ::::::::::
We have four possibilities for $(p,q)$. If $p = \btrue$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{q = \btrue}
   = & \bif{\btrue}{\bif{\btrue}{a}{b}}{\bif{\btrue}{c}{d}} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{c} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\bif{\btrue}{a}{c}}{\bif{\btrue}{b}{d}} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
 &     \let{q = \btrue}
   = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}
\end{eqnarray*}$$
as claimed. If $p = \btrue$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{q = \bfalse}
   = & \bif{\btrue}{\bif{\bfalse}{a}{b}}{\bif{\bfalse}{c}{d}} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\bfalse}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{b}{d} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bif{\btrue}{a}{c}}{\bif{\btrue}{b}{d}} \\
 &     \let{q = \bfalse}
   = & \bif{q}{\bif{\btrue}{a}{c}}{\bif{\btrue}{b}{d}} \\
 &     \let{p = \btrue}
   = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{q = \btrue}
   = & \bif{\bfalse}{\bif{\btrue}{a}{b}}{\bif{\btrue}{c}{d}} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\btrue}{c}{d} \\
 &     \href{@booleans@#cor-if-true}
   = & c \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{a}{c} \\
 &     \let{p = \bfalse}
   = & \bif{p}{a}{c} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
 &     \let{q = \btrue}
   = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{q}{c}{d} \\
 &     \let{q = \bfalse}
   = & \bif{\bfalse}{c}{d} \\
 &     \href{@booleans@#cor-if-false}
   = & d \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{b}{d} \\
 &     \let{p = \bfalse}
   = & \bif{p}{b}{d} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
 &     \let{q = \bfalse}
   = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_nest :: (Boolean b, Equal a)
>   => b -> a -> Test (Bool -> Bool -> a -> a -> a -> a -> Bool)
> _test_if_nest _ _ =
>   testName "if(p,if(q,a,b),if(q,c,d)) == if(q,if(p,a,c),if(p,b,d))" $
>   \p q a b c d ->
>     eq
>       (ifThenElse p (ifThenElse q a b) (ifThenElse q c d))
>       (ifThenElse q (ifThenElse p a c) (ifThenElse p b d))

::::::::::::::::::::
::::::::::::::::::::

Nested ifs on the same boolean can be pruned.

:::::: theorem :::::
[]{#thm-if-prune-true}[]{#thm-if-prune-false}
Let $A$ be a set with $p \in \bool$ and $a,b,c \in A$. We have the following.

1. $\bif{p}{\bif{p}{a}{b}}{c} = \bif{p}{a}{c}$
2. $\bif{p}{a}{\bif{p}{b}{c}} = \bif{p}{a}{c}$

::: proof ::::::::::
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{\bif{\btrue}{a}{b}}{c} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{c} \\
 &     \let{p = \btrue}
   = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{\bif{\bfalse}{a}{b}}{c} \\
 &     \href{@booleans@#cor-if-false}
   = & c \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{a}{c} \\
 &     \let{p = \bfalse}
   = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed.
2. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{a}{\bif{\btrue}{b}{c}} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{c} \\
 &     \let{p = \btrue}
   = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed, and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{a}{\bif{\bfalse}{b}{c}} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{a}{c} \\
 &     \let{p = \bfalse}
   = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_prune_left :: (Boolean b, Equal a)
>   => b -> a -> Test (Bool -> a -> a -> a -> Bool)
> _test_if_prune_left _ _ =
>   testName "if(p,if(p,a,b),c) == if(p,a,c)" $
>   \p a b c -> eq (ifThenElse p (ifThenElse p a b) c) (ifThenElse p a c)
> 
> 
> _test_if_prune_right :: (Boolean b, Equal a)
>   => b -> a -> Test (Bool -> a -> a -> a -> Bool)
> _test_if_prune_right _ _ =
>   testName "if(p,a,if(p,b,c)) == if(p,a,c)" $
>   \p a b c -> eq (ifThenElse p a (ifThenElse p b c)) (ifThenElse p a c)

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ is sort of commutative.

:::::: theorem :::::
[]{#thm-if-commute-true}[]{#thm-if-commute-false}
Let $A$ be a set. For all $p,q \in \bool$ and $a,b \in A$, we have the following.

1. $\bif{p}{a}{\bif{q}{a}{b}} = \bif{q}{a}{\bif{p}{a}{b}}$
2. $\bif{p}{\bif{q}{a}{b}}{b} = \bif{q}{\bif{p}{a}{b}}{b}$

::: proof ::::::::::
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{a}{\bif{q}{a}{b}} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#thm-if-same}
   = & \bif{q}{a}{a} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{q}{a}{\bif{\btrue}{a}{c}} \\
 &     \let{p = \btrue}
   = & \bif{q}{a}{\bif{p}{a}{c}}
\end{eqnarray*}$$
as claimed. If $q = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{q}{a}{\bif{p}{a}{b}} \\
 &     \let{q = \btrue}
   = & \bif{\btrue}{a}{\bif{p}{a}{b}} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#thm-if-same}
   = & \bif{p}{a}{a} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{p}{a}{\bif{\btrue}{a}{c}} \\
 &     \let{q = \btrue}
   = & \bif{p}{a}{\bif{q}{a}{c}}
\end{eqnarray*}$$
as claimed. Suppose then that $p = q = \bfalse$; now
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{a}{\bif{q}{a}{b}} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{q}{a}{b} \\
 &     \let{q = \bfalse}
   = & \bif{\bfalse}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{a}{b} \\
 &     \let{p = \bfalse}
   = & \bif{p}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{a}{\bif{p}{a}{b}} \\
 &     \let{q = \bfalse}
   = & \bif{q}{a}{\bif{p}{a}{b}}
\end{eqnarray*}$$
as claimed.
2. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{b} \\
 &     \let{p = \bfalse}
   = & \bif{\bfalse}{\bif{q}{a}{b}}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#thm-if-same}
   = & \bif{q}{b}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{q}{\bif{\bfalse}{a}{b}}{b} \\
 &     \let{p = \bfalse}
   = & \bif{q}{\bif{p}{a}{b}}{b}
\end{eqnarray*}$$
as claimed. If $q = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{b} \\
 &     \let{q = \bfalse}
   = & \bif{p}{\bif{\bfalse}{a}{b}}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{p}{b}{b} \\
 &     \href{@booleans@#thm-if-same}
   = & b \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bif{p}{a}{b}}{b} \\
 &     \let{q = \bfalse}
   = & \bif{q}{\bif{p}{a}{b}}{b}
\end{eqnarray*}$$
as claimed. If $p = q = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{b} \\
 &     \let{q = \btrue}
   = & \bif{p}{\bif{\btrue}{a}{b}}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{p}{a}{b} \\
 &     \let{p = \btrue}
   = & \bif{\btrue}{a}{b} \\
 &     \let{q = \btrue}
   = & \bif{q}{a}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{q}{\bif{\btrue}{a}{b}}{b} \\
 &     \let{p = \btrue}
   = & \bif{q}{\bif{p}{a}{b}}{b}
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_commute_left :: (Equal a, Boolean b)
>   => b -> a -> Test (Bool -> Bool -> a -> a -> Bool)
> _test_if_commute_left _ _ =
>   testName "if(p,a,if(q,a,b)) == if(q,a,if(p,a,b))" $
>   \p q a b -> eq
>     (ifThenElse p a (ifThenElse q a b))
>     (ifThenElse q a (ifThenElse p a b))
> 
> _test_if_commute_right :: (Equal a, Boolean b)
>   => b -> a -> Test (Bool -> Bool -> a -> a -> Bool)
> _test_if_commute_right _ _ =
>   testName "if(p,if(q,a,b),b) == if(q,if(p,a,b),b)" $
>   \p q a b -> eq
>     (ifThenElse p (ifThenElse q a b) b)
>     (ifThenElse q (ifThenElse p a b) b)

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ interacts with functions of two arguments.

:::::: theorem :::::
[]{#thm-if-func-two}
We have $$f(\bif{p}{a}{c},\bif{p}{b}{d}) = \bif{p}{f(a,b)}{f(c,d)}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 &     \let{p = \btrue}
   = & f(\bif{\btrue}{a}{c},\bif{\btrue}{b}{d}) \\
 &     \href{@booleans@#cor-if-true}
   = & f(a,\bif{\btrue}{b}{d}) \\
 &     \href{@booleans@#cor-if-true}
   = & f(a,b)
\end{eqnarray*}$$
and if $p = \bfalse$,
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 &     \let{p = \bfalse}
   = & f(\bif{\bfalse}{a}{c},\bif{\bfalse}{b}{d}) \\
 &     \href{@booleans@#cor-if-false}
   = & f(c,\bif{\bfalse}{b}{d}) \\
 &     \href{@booleans@#cor-if-false}
   = & f(c,d)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_two_args :: (Equal a, Boolean b)
>   => b -> a -> Test ((a -> a -> a) -> Bool -> a -> a -> a -> a -> Bool)
> _test_if_two_args _ _ =
>   testName "f(if(p,a,c),if(p,b,x)) == if(p,f(a,b),f(c,d))" $
>   \f p a b c d -> eq
>     (f (if p then a else c) (if p then b else d))
>     (if p then f a b else f c d)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_boolean ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName b, Equal b, Show b, Arbitrary b, CoArbitrary b, Boolean b
>   ) => Int -> Int -> b -> a -> IO ()
> 
> _test_boolean size cases p x = do
>   testLabel2 "Boolean" p x
>   let args = testArgs size cases
> 
>   runTest args (_test_if_true p x)
>   runTest args (_test_if_false p x)
>   runTest args (_test_if_same p x)
>   runTest args (_test_if_func p x)
>   runTest args (_test_if_nest p x)
>   runTest args (_test_if_prune_left p x)
>   runTest args (_test_if_prune_right p x)
>   runTest args (_test_if_commute_left p x)
>   runTest args (_test_if_commute_right p x)
>   runTest args (_test_if_two_args p x)

Main:

> main_boolean :: IO ()
> main_boolean = do
>   let a = true :: Bool
>   _test_boolean   20 100 a a
> 
>   _test_functions 20 100 a a a a
>   _test_flip      a a a a a a a 20 100
>   _test_clone     20 100 a a
