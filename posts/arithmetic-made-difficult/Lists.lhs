---
title: Lists
author: nbloomf
date: 2017-04-23
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Lists
>   ( List(..), ListShape(..), ListOf(..), ConsList()
>   , isNil, tail, foldr, uncons
>   ) where
> 
> import Booleans
> 
> import Prelude ((++), return, undefined)
> 
> import Test.QuickCheck

In the previous post, we saw how the process of describing $\nats$ in terms of its universal map $\natrec{\ast}{\ast}$ can be generalized: take an endofunctor $F$, assume it has an initial algebra, and see how it behaves.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, and define a functor $F_A$ by $F_A(X) = 1 + A \times X$. We assume that $F_A$ has an initial algebra, which we will denote $\lists{A}$. We denote the component maps of the isomorphism $$\theta : 1 + A \times \lists{A} \rightarrow \lists{A}$$ by $\nil : 1 \rightarrow \lists{A}$ and $\cons : A \times \lists{A} \rightarrow \lists{A}$.
</p></div>
</div>

The names *nil* and *cons* come from the Lisp programming language, where they were first introduced. Now because the algebra map $\nil + \cons$ is an isomorphism, we have

<div class="result">
<div class="thm"><p>
If $x \in \lists{A}$, then either $x = \nil$ or $x = \cons(a,y)$ for some $a \in A$ and $y \in \lists{A}$.
</p></div>
</div>

So what do the elements of $\lists{A}$ look like? Well, applying our "constructor" functions we can build elements like
$$\begin{array}{c}
\nil \\
\cons(a,\nil) \\
\cons(b,\cons(a,\nil)) \\
\cons(c,\cons(b,\cons(a,\nil))) \\
\vdots
\end{array}$$

We will wrap this definition up in code both as a concrete type and as a type class, so that later we can give alternative implementations.

First the concrete type:

> data ConsList a = N | C a (ConsList a)
> 
>  
> instance (Show a) => Show (ConsList a) where
>   show N        = "()"
>   show (C x xs) = "(" ++ show x ++ show xs ++ ")"
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
>   shrink (C _ x) = [x]

And the class:

> data ListShape a t
>   = Nil
>   | Cons a (t a)
>   deriving Show
> 
> class List t where
>   toConsList   :: t a -> ConsList a
>   fromConsList :: ConsList a -> t a
> 
>   nil :: t a
> 
>   cons :: a -> t a -> t a
> 
>   listShape :: t a -> ListShape a t
>   listShape x = case listShape (toConsList x) of
>     Nil       -> Nil
>     Cons a as -> Cons a (fromConsList as)
> 
>   list :: [a] -> t a
>   list xs = fromConsList (list xs)
> 
> 
> isNil :: (List t) => t a -> Bool
> isNil x = case listShape x of
>   Nil      -> True
>   Cons _ _ -> False

And the instance.

> instance List ConsList where
>   toConsList   = id
>   fromConsList = id
>
>   nil  = N
>   cons = C
> 
>   listShape  N      = Nil
>   listShape (C a x) = Cons a x
> 
>   list m = case m of
>     []     -> N
>     (x:xs) -> C x (list xs)

This business about initial algebras is nice, but it will be convenient to unpack this definition a little bit. First, we give the following more concrete description of $F_A$-algebras:

<div class="result">
<div class="defn"><p>
($A$-inductive set.) Let $A$ be a set. An $A$-inductive set is a set $B$ together with an element $e$ and a mapping $f : A \times B \rightarrow B$.
</p></div>
</div>

And a more concrete decription of $F_A$-algebra morphisms:

<div class="result">
<div class="defn"><p>
($A$-inductive set homomorphism.) Let $A$ be a set. Given two $A$-inductive sets $(B,e,f)$ and $(C,u,g)$, an $A$-inductive set homomorphism is a mapping $\varphi : B \rightarrow C$ such that $\varphi(e) = u$ and $$\varphi(f(a,x)) = g(a,\varphi(x))$$ for all $a \in A$ and $x \in B$.
</p></div>
</div>

And finally, a more concrete description of the universal algebra from $\lists{A}$.

<div class="result">
<div class="thm"><p>
(Fold.) Let $A$ be a set, and let $(B,e,\varphi)$ be an $A$-inductive set. Then there is a unique map $\Theta : \lists{A} \rightarrow B$ such that $$\Theta(\nil) = e$$ and $$\Theta(\cons(a,x)) = \varphi(a,\Theta(x)).$$ We denote this unique $\Theta$ by $\foldr{e}{\varphi}$.
</p></div>
</div>

It's handy to remember that this theorems says not only that foldr exists, but that it is unique -- in some sense foldr gives the unique solution to a system of functional equations. This gives us a strategy for showing that two programs are equivalent. If one is defined as a fold, and both programs satisfy the universal property, then they have to be equal. This is nice for showing, for instance, that a *slow but obviously correct* program is equivalent to a *fast but not obviously correct* one.

Here is a naive implementation of $\foldr{\ast}{\ast}$.

> foldr :: (List t) => b -> (a -> b -> b) -> t a -> b
> foldr e phi x = case listShape x of
>   Nil       -> e
>   Cons a as -> phi a (foldr e phi as)

Note that this definition is *not* tail recursive. This turns out not to be a huge problem in practice.

Now $\nil$ is not equal to $\cons(-,-)$:

<div class="result">
<div class="thm">
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then $\nil \neq \cons(a,x)$.
</div>

<div class="proof"><p>
Suppose by way of contradiction that $\nil = \cons(a,x)$. Let $e = \btrue$ and define $\varphi : A \times \bool \rightarrow \bool$ by $\varphi(a,p) = \bfalse$. Then we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \foldr{\btrue}{\varphi}(\nil) \\
 & = & \foldr{\btrue}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\btrue}{\varphi}(x)) \\
 & = & \bfalse,
\end{eqnarray*}$$
a contradiction.
</p></div>
</div>

Now $\lists{A}$ has an induction principle.

<div class="result">
<div class="thm">
(List Induction.) Let $A$ be a set, and let $f : \lists{A} \rightarrow B$ be a map. Suppose $C \subseteq B$ is a subset with the property that

1. $f(\nil) \in C$.
2. If $f(x) \in C$ and $a \in A$, then $f(\cons(a,x)) \in C$.

Then we have $f(x) \in C$ for all $x \in \lists{A}$.
</div>

<div class="proof"><p>
This proof is analogous to the proof of the induction principle for $\nats$. We first define $T \subseteq \lists{A}$ by $$T = \{x \in \lists{A} \mid f(x) \in C \}.$$ Note that $\nil \in T$ and if $x \in T$ and $a \in A$ then $\cons(a,x) \in T$; in particular, $(T,\nil,\cons)$ is an $A$-iterative set. We let $\Theta = \foldr{\nil}{\cons}$. Now the inclusion map $\iota : T \rightarrow \lists{A}$ is an $A$-inducive set homomorphism, since $\iota(\nil) = \nil$ and $$\iota(\cons(a,x)) = \cons(a,x) = \cons(a,\iota(x)).$$ Thus $\iota \circ \Theta : \lists{A} \rightarrow \lists{A}$ is an $A$-inductive set homomorphism, so it must be $\id_A$. Thus if $x \in \lists{A}$ we have $$x = \id(x) = \iota(\Theta(x)) = \Theta(x) \in T$$ so that $f(x) \in C$ as claimed.
</p></div>
</div>

Here's an example using list induction.

<div class="result">
<div class="thm">
Let $A$ be a set. Then we have $$\foldr{\nil}{\cons}(x) = x$$ for all $x \in \lists{A}$.
</div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have $$\foldr{\nil}{\cons}(\nil) = nil$$ as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{\nil}{\cons}(\cons(a,x)) \\
 & = & \cons(a,\foldr{\nil}{\cons}(x)) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Here's a helper function.

<div class="result">
<div class="thm">
Let $A$ be a set. Define $\varphi : A \times (\lists{A} \times \lists{A}) \rightarrow \lists{A} \times \lists{A}$ by $\varphi(a,(z,x)) = (x,\cons(a,x))$. Now define $\tail : \lists{A} \rightarrow \lists{A}$ by $$\tail(x) = \fst(\foldr{(\nil,\nil)}{\varphi}(x)).$$ Then we have the following for all $a \in A$ and $x \in \lists{A}$.

1. $\tail(\nil) = \nil$.
2. $\foldr{(\nil,\nil)}{\varphi}(\cons(a,x)) = (x,\cons(a,x))$.
3. $\tail(\cons(a,x)) = x$.
</div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \tail(\nil) \\
 & = & \fst(\foldr{(\nil,\nil)}{\varphi}(\nil)) \\
 & = & \fst(\nil,\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \foldr{(\nil,\nil)}{\varphi}(\cons(a,\nil)) \\
 & = & \varphi(a,\foldr{(\nil,\nil)}{\varphi}(\nil)) \\
 & = & \varphi(a,(\nil,\nil)) \\
 & = & (\nil,\cons(a,\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \foldr{(\nil,\nil)}{\varphi}(\cons(a,\cons(b,x))) \\
 & = & \varphi(a,\foldr{(\nil,\nil)}{\varphi}(\cons(b,x))) \\
 & = & \varphi(a,(x,\cons(b,x))) \\
 & = & (\cons(b,x),\cons(a,\cons(b,x)))
\end{eqnarray*}$$
as needed.
3. We have
$$\begin{eqnarray*}
 &   & \tail(\cons(a,x)) \\
 & = & \fst(\foldr{(\nil,\nil)}{\varphi}(\cons(a,x))) \\
 & = & \fst(x,\cons(a,x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

We could define tail in terms of foldr, but the theorem suggests another way.

> tail :: (List t) => t a -> t a
> tail x = case listShape x of
>   Nil      -> nil
>   Cons _ y -> y

One more bit of wierdness. Just like with ``Natural``, even though it makes sense to define an ``Equal`` instance against ``ListOf``, the naive way to do it,

```haskell
instance (Equal a, ListOf t) => Equal (t a) where
  ...
```

is undecidable. But we can get around this with a simple wrapper type:

> newtype ListOf t a = ListOf { unListOf :: t a }
> 
> 
> instance (List t) => List (ListOf t) where
>   toConsList   = toConsList . unListOf
>   fromConsList = ListOf . fromConsList
> 
>   nil      = ListOf nil
>   cons a x = ListOf (cons a (unListOf x))
> 
> 
> instance (List t, Show a) => Show (ListOf t a) where
>   show = show . toConsList
> 
> instance (List t, Arbitrary a) => Arbitrary (ListOf t a) where
>   arbitrary = do
>     x <- arbitrary
>     return (ListOf (fromConsList x))

Recall that the "constructor" map $F(X) \rightarrow X$ of an initial $F$-algebra $X$ is an isomorphism, so it must have an inverse. What is this inverse for $\lists{A}$? The signature is $$f : \lists{A} \rightarrow \ast + A \times \lists{A}.$$ And we expect that
$$\begin{eqnarray*}
 &   & \ast \\
 & = & (f \circ \theta)(\ast) \\
 & = & f(\theta(\ast)) \\
 & = & f(\nil),
\end{eqnarray*}$$
and similarly
$$\begin{eqnarray*}
 &   & (a,x) \\
 & = & (f \circ \theta)(a,x) \\
 & = & f(\theta(a,x)) \\
 & = & f(\cons(a,x)).
\end{eqnarray*}$$
With this in mind, we will call this $f$ $\uncons$.

<div class="result">
<div class="defn">
Let $A$ be a set. We define $$\uncons : \lists{A} \rightarrow \ast + A \times \lists{A}$$ by $$\uncons(x) = \left\{\begin{array}{ll} \ast & \mathrm{if}\ x = \nil \\ (a,u) & \mathrm{if}\ x = \cons(a,u). \end{array}\right.$$
</div>
</div>

In Haskell:

> uncons :: (List t) => t a -> Maybe (a, t a)
> uncons x = case listShape x of
>   Nil      -> Nothing
>   Cons a u -> Just (a,u)


Equality
--------

And some properties of equality:

<div class="result">
<div class="thm">
Let $A$ be a set. We have the following for all $a,b \in A$ and $x,y \in \lists{A}$.

1. $\nil \neq \cons(a,x)$.
2. $\cons(a,x) = \cons(b,y)$ if and only if $a = b$ and $x = y$.
</div>

<div class="proof"><p>
1. Define $\varphi : A \times \bool \rightarrow \bool$ by $\varphi(a,b) = \btrue$. Suppose $\nil = \cons(a,x)$, and consider $\foldr{\bfalse}{\varphi}$. We have
$$\begin{eqnarray*}
 &   & \bfalse \\
 & = & \foldr{\bfalse}{\varphi}(\nil) \\
 & = & \foldr{\bfalse}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\bfalse}{\varphi}(x)) \\
 & = & \btrue,
\end{eqnarray*}$$
which is absurd.
2. The "if" part is clear. Now suppose we have $\cons(a,x) = \cons(b,y)$. Define $\varphi : A \times A \rightarrow A$ by $\varphi(u,v) = u$, and consider $\foldr{a}{\varphi}$. We have
$$\begin{eqnarray*}
 &   & a \\
 & = & \varphi(a,\foldr{a}{\varphi}(x)) \\
 & = & \foldr{a}{\varphi}(\cons(a,x)) \\
 & = & \foldr{a}{\varphi}(\cons(b,y)) \\
 & = & \varphi(b,\foldr{a}{\varphi}(y)) \\
 & = & b
\end{eqnarray*}$$
as claimed. Finally, we have
$$\begin{eqnarray*}
 &   & x \\
 & = & \tail(\cons(a,x)) \\
 & = & \tail(\cons(b,y)) \\
 & = & y
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

> instance (List t, Equal a) => Equal (ListOf t a) where
>   eq x y = case (listShape x, listShape y) of
>     (Nil,      Nil     ) -> True
>     (Nil,      Cons _ _) -> False
>     (Cons _ _, Nil     ) -> False
>     (Cons a u, Cons b v) -> (eq a b) &&& (eq u v)

Another example:

<div class="result">
<div class="thm">
Let $A$ be a set with $a \in A$ and $x \in \lists{A}$. Then $x \neq \cons(a,x)$.
</div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have $\nil \neq \cons(a,\nil)$ as needed. For the inductive step, suppose the inequality holds for some $x$ and let $b \in A$. Suppose further by way of contradiction that $\cons(b,x) = \cons(a,\cons(b,x))$. Then we have $a = b$ and $x = \cons(b,x)$, a contradiction. So in fact $\cons(b,x) \neq \cons(a,\cons(b,x))$ as needed.
</p></div>
</div>
