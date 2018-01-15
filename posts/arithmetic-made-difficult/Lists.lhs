---
title: Lists
author: nbloomf
date: 2017-04-23
tags: arithmetic-made-difficult, literate-haskell
slug: lists
---

> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE NoImplicitPrelude #-}
> module Lists
>   ( List(..), ConsList(), foldr
>   ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import DisjointUnions

In the previous post, we saw how the process of describing $\nats$ in terms of its universal map $\natrec{\ast}{\ast}$ can be generalized: take an endofunctor $F$, assume it has an initial algebra, and see how it behaves. Here's an example.

:::::: definition ::
Let $A$ be a set, and define a functor $F_A$ by $F_A(X) = 1 + A \times X$. We assume that $F_A$ has an initial algebra, which we will denote $\lists{A}$. We denote the component maps of the isomorphism $$\theta : 1 + A \times \lists{A} \rightarrow \lists{A}$$ by $\const(\nil) : 1 \rightarrow \lists{A}$ and $\cons : A \times \lists{A} \rightarrow \lists{A}$. That is, $$\Theta = \either(\const(\nil),\cons).$$
::::::::::::::::::::
::::::::::::::::::::

The names *nil* and *cons* come from the Lisp programming language, where they were first introduced. Now because the algebra map $\nil + \cons$ is an isomorphism, it has an inverse; we'll denote this map $\uncons : \lists{A} \rightarrow 1 + \lists{A}$.

:::::: theorem :::::
Let $A$ be a set. Then we have the following.

1. $\uncons(\nil) = \lft(\ast)$.
2. $\uncons(\cons(a,x)) = \rgt((a,x))$.
::::::::::::::::::::

::: proof ::::::::::
1. We have
$$\begin{eqnarray*}
 &   & \lft(\ast) \\
 & = & \id(\lft(\ast)) \\
 & = & (\uncons \circ \either(\const(\nil),\cons))(\lft(\ast)) \\
 & = & \uncons(\either(\const(\nil),\cons)(\lft(\ast))) \\
 & = & \uncons(\const(\nil)(\ast)) \\
 & = & \uncons(\nil)
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \rgt((a,x)) \\
 & = & (\uncons \circ \either(\const(\nil),\cons))(\rgt((a,x))) \\
 & = & \uncons(\either(\const(\nil),\cons)(\rgt((a,x)))) \\
 & = & \uncons(\cons(a,x))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::

As a corollary, we can use $\uncons$ to characterize equality for lists.

:::::: corollary :::
Let $A$ be a set. Then we have the following.

1. Every element of $\lists{A}$ is equal to either $\nil$ or to $\cons(a,x)$ for some $a \in A$ and $x \in \lists{A}$.
2. $\nil$ and $\cons(a,x)$ are not equal for any $a$ and $x$.
3. $\cons(a,x) = \cons(b,y)$ if and only if $a = b$ and $x = y$.
::::::::::::::::::::

::: proof ::::::::::
1. Let $z \in \lists{A}$. We have two possibilities for $\uncons(z)$. If $\uncons(z) = \lft(\ast)$, then
$$\begin{eqnarray*}
 &   & z \\
 & = & (\either(\const(\nil),\cons) \circ \uncons)(z) \\
 & = & \either(\const(\nil),\cons)(\lft(\ast)) \\
 & = & \const(\nil)(\ast) \\
 & = & \nil,
\end{eqnarray*}$$
and if $\uncons(z) = \rgt(a,x)$, then
$$\begin{eqnarray*}
 &   & z \\
 & = & (\either(\const(\nil),\cons) \circ \uncons)(z) \\
 & = & \either(\const(\nil),\cons)(\rgt((a,x))) \\
 & = & \cons(a,x) \\
\end{eqnarray*}$$
as claimed.
2. If $\nil = \cons(a,x)$, we have
$$\begin{eqnarray*}
 &   & \lft(\ast) \\
 & = & \uncons(\nil) \\
 & = & \uncons(\cons(a,x)) \\
 & = & \rgt((a,x)),
\end{eqnarray*}$$
which is absurd.
3. The "if" direction is clear. To see the "only if" direction, suppose $\cons(a,x) = \cons(b,y)$. Then we have
$$\begin{eqnarray*}
 &   & \rgt((a,x)) \\
 & = & \uncons(\cons(a,x)) \\
 & = & \uncons(\cons(b,y)) \\
 & = & \rgt((b,y)),
\end{eqnarray*}$$
so that $(a,x) = (b,y)$, and thus $a = b$ and $x = y$ as claimed.
::::::::::::::::::::
::::::::::::::::::::

So what do the elements of $\lists{A}$ look like? Well, applying our "constructor" functions we can build elements like
$$\begin{array}{c}
\nil \\
\cons(a,\nil) \\
\cons(b,\cons(a,\nil)) \\
\cons(c,\cons(b,\cons(a,\nil))) \\
\vdots
\end{array}$$
We will wrap this definition up in code both as a concrete type and as a type class, so that later we can give alternative implementations. The list algebra is characterized by the components of the algebra map ($\nil$ and $\cons$) as well as the inverse map $\uncons$).

> class List t where 
>   nil :: t a
> 
>   cons :: a -> t a -> t a
> 
>   uncons :: t a -> Either () (a, t a)
> 
>   list :: [a] -> t a

And the concrete type:

> data ConsList a = N | C a (ConsList a)
>   deriving Show
> 
> 
> instance List ConsList where
>   nil  = N
> 
>   cons = C
> 
>   uncons m = case m of
>     N     -> lft ()
>     C a x -> rgt (a,x)
> 
>   list m = case m of
>     []     -> N
>     (x:xs) -> C x (list xs)
> 
> 
> instance (Equal a) => Equal (ConsList a) where
>   eq N       N       = true
>   eq N       (C _ _) = false
>   eq (C _ _) N       = false
>   eq (C a x) (C b y) = and (eq a b) (eq x y)
> 
> 
> instance (TypeName a) => TypeName (ConsList a) where
>   typeName _ = "ConsList " ++ (typeName (undefined :: a))
> 
> 
> instance (Arbitrary a) => Arbitrary (ConsList a) where
>   arbitrary = do
>     xs <- arbitrary
>     return (list xs)
> 
>   shrink  N      = []
>   shrink (C a x) = [x]
> 
> 
> instance (Arbitrary a) => CoArbitrary (ConsList a) where
>   coarbitrary N = variant 0
>   coarbitrary (C a x) = variant 1 . coarbitrary x

This business about initial algebras is nice, but it will be convenient to unpack this definition a little bit. First, we give the following more concrete description of $F_A$-algebras:

:::::: definition ::
($A$-inductive set.) Let $A$ be a set. An $A$-inductive set is a set $B$ together with an element $e$ and a mapping $f : A \times B \rightarrow B$.
::::::::::::::::::::
::::::::::::::::::::

And a more concrete decription of $F_A$-algebra morphisms:

:::::: definition ::
($A$-inductive set homomorphism.) Let $A$ be a set. Given two $A$-inductive sets $(B,e,f)$ and $(C,u,g)$, an $A$-inductive set homomorphism is a mapping $\varphi : B \rightarrow C$ such that $\varphi(e) = u$ and $$\varphi(f(a,x)) = g(a,\varphi(x))$$ for all $a \in A$ and $x \in B$.
::::::::::::::::::::
::::::::::::::::::::

And finally, a more concrete description of the universal algebra from $\lists{A}$.

:::::: theorem :::::
(Fold.) Let $A$ be a set, and let $(B,e,\varphi)$ be an $A$-inductive set. Then there is a unique map $\Theta : \lists{A} \rightarrow B$ which solves the system of functional equations $$\left\{ \begin{array}{l} \Theta(\nil) = e \\ \Theta(\cons(a,x)) = \varphi(a,\Theta(x)). \end{array} \right.$$ We denote this unique $\Theta$ by $\foldr{e}{\varphi}$.

In Haskell:

> foldr :: (List t) => b -> (a -> b -> b) -> t a -> b
> foldr e phi x = case uncons x of
>   Left ()      -> e
>   Right (a,as) -> phi a (foldr e phi as)

::::::::::::::::::::
::::::::::::::::::::

Note that this definition is *not* tail recursive. This turns out not to be a huge problem in practice.

It's handy to remember that this theorem says not only that $\foldr{\ast}{\ast}$ exists, but that it is unique -- in some sense foldr gives the unique solution to a system of functional equations. This gives us a strategy for showing that two programs are equivalent. If one is defined as a fold, and both programs satisfy the universal property, then they have to be equal. This is nice for showing, for instance, that a *slow but obviously correct* program is equivalent to a *fast but not obviously correct* one.

Now $\lists{A}$ has an inductive proof strategy.

:::::: theorem :::::
(List Induction.) Let $A$ be a set, and let $f : \lists{A} \rightarrow B$ be a map. Suppose $C \subseteq B$ is a subset with the property that

1. $f(\nil) \in C$.
2. If $f(x) \in C$ and $a \in A$, then $f(\cons(a,x)) \in C$.

Then we have $f(x) \in C$ for all $x \in \lists{A}$.
::::::::::::::::::::

::: proof ::::::::::
This proof is analogous to the proof of the induction principle for $\nats$. We first define $T \subseteq \lists{A}$ by $$T = \{x \in \lists{A} \mid f(x) \in C \}.$$ Note that $\nil \in T$ and if $x \in T$ and $a \in A$ then $\cons(a,x) \in T$; in particular, $(T,\nil,\cons)$ is an $A$-iterative set. We let $\Theta = \foldr{\nil}{\cons}$. Now the inclusion map $\iota : T \rightarrow \lists{A}$ is an $A$-inducive set homomorphism, since $\iota(\nil) = \nil$ and $$\iota(\cons(a,x)) = \cons(a,x) = \cons(a,\iota(x)).$$ Thus $\iota \circ \Theta : \lists{A} \rightarrow \lists{A}$ is an $A$-inductive set homomorphism, so it must be $\id_A$. Thus if $x \in \lists{A}$ we have $$x = \id(x) = \iota(\Theta(x)) = \Theta(x) \in T$$ so that $f(x) \in C$ as claimed.
::::::::::::::::::::
::::::::::::::::::::

Here's an example using list induction.

:::::: theorem :::::
Let $A$ be a set. Then we have $$\foldr{\nil}{\cons}(x) = x$$ for all $x \in \lists{A}$.
::::::::::::::::::::

::: proof ::::::::::
We proceed by list induction on $x$. For the base case $x = \nil$, we have $$\foldr{\nil}{\cons}(\nil) = \nil$$ as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\cons}(\cons(a,x)) \\
 & = & \cons(a,\foldr{\nil}{\cons}(x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::
::::::::::::::::::::
