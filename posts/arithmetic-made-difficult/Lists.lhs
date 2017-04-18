---
title: Lists
author: nbloomf
date: 2017-04-23
tags: arithmetic-made-difficult, literate-haskell
---

> module Lists
>   ( List(), ListOf(..), ListShape(..)
>   ) where
> 
> import Test.QuickCheck

In the previous post, we saw how the process of describing $\nats$ in terms of its universal map $\natrec{\ast}{\ast}$ can be generalized: take an endofunctor $F$, assume it has an initial algebra, and see how it behaves.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, and define a functor $F_A$ by $F_A(X) = 1 + A \times X$. We assume that $F_A$ has an initial algebra, which we will denote $\lists{A}$. We denote the component maps of the isomorphism $$\theta : 1 + A \times \lists{A} \rightarrow \lists{A}$$ by $\nil : 1 \rightarrow \lists{A}$ and $\cons : A \times \lists{A} \rightarrow \lists{A}$.
</p></div>
</div>

Because the algebra map $\nil + \cons$ is an isomorphism, we have

<div class="result">
<div class="thm"><p>
If $x \in \lists{A}$, then either $x = \nil$ or $x = \cons(a,y)$ for some $a \in A$ and $y \in \lists{A}$.
</p></div>
</div>

We will wrap this definition up in code both as a concrete type and as a type class, so that later we can give alternative implementations.

First the concrete type:

> data List a = N | C a (List a)

And the class:

> data ListShape a t = Nil | Cons a (t a)
> 
> class ListOf t where
>   toList :: t a -> List a
>   fromList :: List a -> t a
> 
>   nil :: t a
> 
>   cons :: a -> t a -> t a
> 
>   listShape :: t a -> ListShape a t
>   listShape x = case listShape $ toList x of
>     Nil       -> Nil
>     Cons a as -> Cons a (fromList as)
> 
>   isNil :: t a -> Bool
>   isNil x = case listShape x of
>     Nil      -> True
>     Cons _ _ -> False
> 
>   list :: [a] -> t a
>   list xs = fromList $ list xs

And the instance.

> instance ListOf List where
>   toList = id
>   fromList = id
>
>   nil = N
>   cons = C
>   listShape x = case x of
>     N      -> Nil
>     C a as -> Cons a as
> 
>   list m = case m of
>     []     -> N
>     (x:xs) -> C x (list xs)

This business about initial algebras is nice, but it will be convenient to unpack this definition a little bit. First, we give the following more concrete description of $F_A$-algebras:

<div class="result">
<div class="defn"><p>
($A$-inductive set.) Let $A$ be a set. And $A$-inductive set is a set $B$ together with an element $e$ and a mapping $f : A \times B \rightarrow B$.
</p></div>
</div>

And a more concrete decription of $F_A$-algebra morphisms:

<div class="result">
<div class="defn"><p>
($A$-inductive set homomorphism.) Let $A$ be a set. Given two $A$-inductive sets $(B,e,f)$ and $(C,u,g)$, an $A$-inductive set homomorphism is a mapping $\varphi : B \rightarrow C$ such that $\varphi(e) = u$ and $\varphi(f(a,x)) = g(a,\varphi(x))$ for all $a \in A$ and $x \in B$.
</p></div>
</div>

And finally, a more concrete description of the universal algebra from $\lists{A}$.

<div class="result">
<div class="thm"><p>
(Fold.) Let $A$ be a set, and let $(B,e,\varphi)$ be an $A$-inductive set. Then there is a unique map $\Theta : \lists{A} \rightarrow B$ such that $$\Theta(\nil) = e$$ and $$\Theta(\cons(a,x)) = \varphi(a,\Theta(x)).$$ We denote this unique $\Theta$ by $\fold{e}{\varphi}$.
</p></div>
</div>

> fold :: (ListOf t) => b -> (a -> b -> b) -> t a -> b
> fold e phi x = undefined
