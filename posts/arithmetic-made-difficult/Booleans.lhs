---
title: Booleans
author: nbloomf
date: 2014-04-01
tags: arithmetic-made-difficult, literate-haskell
slug: booleans
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Booleans
>   ( Boolean, true, false, ifThenElse, isTrue, isFalse, Equal, eq
>   , _test_boolean, main_boolean
>   ) where
> 
> import Prelude (Bool(True, False))
> import Testing

Before we think about numbers or writing programs, let's start by nailing down some important ideas about truth values. In math there can be a kind of other-worldness about true and false, since they live in the "metalanguage" of mathematical logic rather than the "object language" of whatever we are studying. But it will turn out to be useful to algebraify the truth values themselves.

We're going to characterize the boolean values true and false in a roundabout way. First, we define a kind of algebra.

:::::: definition ::
[](#def-doubly-pointed-set) A *doubly-pointed set* is a set $A$ with two (not necessarily distinct) distinguished elements $a_t, a_f \in A$. If $A$ and $B$ are doubly-pointed sets with distinguished elements $a_t, a_f \in A$ and $b_t, b_f \in B$, a map $\theta : A \rightarrow B$ is called a *doubly-pointed homomorphism* if $\theta(a_t) = b_t$ and $\theta(a_f) = b_f$.
::::::::::::::::::::

As algebras go, doubly-pointed sets are almost as weak as they come. We can see shades of the boolean values there -- "true" and "false" can be thought of as distinguished elements  in a doubly-pointed set. And indeed we'll do that. But the booleans are not just any doubly-pointed set; they are the *smallest* such set in a precise sense.

:::::: definition ::
[]{#def-bool}[]{#cor-if-true}[]{#cor-if-false} There is a special doubly-pointed set, denoted $\bool$, with distinguished elements $\btrue$ and $\bfalse$, with the property that if $A$ is a doubly-pointed set with distinguished elements $a_t, a_f$, then there is a *unique* doubly-pointed homomorphism $\Theta : \bool \rightarrow A$. We denote this $\Theta$ by $$\Theta(p) = \bif{p}{a_t}{a_f}.$$ To be clear, we have $$\bif{\btrue}{a_t}{a_f} = a_t$$ and $$\bif{\bfalse}{a_t}{a_f} = a_f.$$
::::::::::::::::::::

What makes the booleans special among doubly-pointed sets is this unique map, which looks suspiciously like the traditional "if-then-else" construct, because that's exactly what it is.

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

We can test this instance. Remember the defining property of $\bif{\ast}{\ast}{\ast}$ is that it preserves distinguished points.

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

It will be handy later to name these two functions from an abstract boolean set to ``Bool``.

> isTrue :: (Boolean b) => b -> Bool
> isTrue p = ifThenElse p true false
> 
> isFalse :: (Boolean b) => b -> Bool
> isFalse p = ifThenElse p false true

There are many other instances which differ only by the labels of $\btrue$ and $\bfalse$, and depending on the context, a different concrete instance might make more sense. We could call the distinguished elements of $\bool$ "Yes/No", "Present/Absent", or something else, and the essence of booleanness would not change.

$\bif{\ast}{\ast}{\ast}$ enjoys some other nice properties. For example, it interacts with function application.

:::::: theorem :::::
[]{#thm-iffunc}
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $p \in \bool$ and $u,v \in A$, we have $$f(\bif{p}{u}{v}) = \bif{p}{f(u)}{f(v)}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\btrue}{u}{v}) \\
 &     \href{@booleans@#cor-if-true}
   = & f(u) \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\bfalse}{u}{v}) \\
 &     \href{@booleans@#cor-if-false}
   = & f(v) \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
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
[](#thm-ifnest) Let $A$ be a set with $p,q \in \bool$ and $a,b,c,d \in A$. Then we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}.
\end{eqnarray*}$$

::: proof ::::::::::
We have four possibilities for $(p,q)$. If $p = \btrue$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\btrue}{a}{b}}{\bif{q}{c}{d}} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{b} \\
 &     \href{@booleans@#cor-if-true}
   = & a \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{a}{c} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{\bif{\btrue}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \btrue$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{b}}{\bif{q}{c}{d}} \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\bfalse}{a}{b} \\
 &     \href{@booleans@#cor-if-false}
   = & b \\
 &     \href{@booleans@#cor-if-true}
   = & \bif{\btrue}{b}{d} \\
 &     \href{@booleans@#cor-if-false}
   = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\btrue}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\btrue}{c}{d}} \\
 & = & \bif{\btrue}{c}{d} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\bfalse}{c}{d}} \\
 & = & \bif{\bfalse}{c}{d} \\
 & = & d \\
 & = & \bif{\bfalse}{b}{d} \\
 & = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\bfalse}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
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
[](#thm-ifprune) Let $A$ be a set with $p \in \bool$ and $a,b,c \in A$. We have the following.

1. $\bif{p}{\bif{p}{a}{b}}{c} = \bif{p}{a}{c}$
2. $\bif{p}{a}{\bif{p}{b}{c}} = \bif{p}{a}{c}$

::: proof ::::::::::
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{p}{\bif{\btrue}{a}{b}}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{\bfalse}{\bif{\bfalse}{a}{b}}{c} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed.
2. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{\btrue}{a}{\bif{p}{b}{c}} \\
 & = & a \\
 & = & \bif{\btrue}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed, and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{p}{a}{\bif{\bfalse}{b}{c}} \\
 & = & \bif{p}{a}{c}
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
Let $A$ be a set. For all $p,q \in \bool$ and $a,b \in A$, we have the following.

1. $\bif{p}{a}{\bif{q}{a}{b}} = \bif{q}{a}{\bif{p}{a}{b}}$
2. $\bif{p}{\bif{q}{a}{b}}{b} = \bif{q}{\bif{p}{a}{b}}{b}$

::: proof ::::::::::
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & a \\
 & = & \bif{q}{a}{a} \\
 & = & \bif{q}{a}{\bif{p}{a}{c}}
\end{eqnarray*}$$
as claimed. Likewise, the equality holds if $q = \btrue$. Suppose then that $p = q = \bfalse$; now
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & \bif{q}{a}{b} \\
 & = & b \\
 & = & \bif{p}{a}{b} \\
 & = & \bif{q}{a}{\bif{p}{a}{b}}
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{b} \\
 & = & \bif{\bnot(p)}{b}{\bif{q}{a}{b}} \\
 & = & \bif{\bnot(p)}{b}{\bif{\bnot(q)}{b}{a}} \\
 & = & \bif{\bnot(q)}{b}{\bif{\bnot(p)}{b}{a}} \\
 & = & \bif{\bnot(q)}{b}{\bif{p}{a}{b}} \\
 & = & \bif{q}{\bif{p}{a}{b}}{b}
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
We have $$f(\bif{p}{a}{c},\bif{p}{b}{d}) = \bif{p}{f(a,b)}{f(c,d)}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 & = & f(a,b)
\end{eqnarray*}$$
and if $p = \bfalse,
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 & = & f(c,d)
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


Equality
--------

Now that we've algebraified truth values, we will also algebraify equality. Typically I think of equality (as in the $=$ symbol) as a metalanguage expression. Sure, we can define a relation that captures equality on a given set, but really equality is a "logical" thing, not a "mathematical" one. We'll express this using a type class in Haskell like so.

> class Equal a where
>   eq :: (Boolean b) => a -> a -> b

(Why not use the built in `Eq` class? No good reason.) For example, here is the ``Equal`` instance for ``Bool``:

> instance Equal Bool where
>   eq p q = ifThenElse p (ifThenElse q true false) (ifThenElse q false true)
> 
> instance Equal () where
>   eq () () = true


Testing
-------

Suite:

> _test_boolean ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a
>   , Boolean b, Arbitrary b, Show b, Equal b, TypeName b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_boolean p x size num = do
>   testLabel1 "Boolean" p
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_if_true p x)
>   runTest args (_test_if_false p x)
>   runTest args (_test_if_func p x)
>   runTest args (_test_if_nest p x)
>   runTest args (_test_if_prune_left p x)
>   runTest args (_test_if_prune_right p x)
>   runTest args (_test_if_commute_left p x)
>   runTest args (_test_if_commute_right p x)
>   runTest args (_test_if_two_args p x)

Main:

> main_boolean :: IO ()
> main_boolean = _test_boolean (true :: Bool) (true :: Bool) 20 100
