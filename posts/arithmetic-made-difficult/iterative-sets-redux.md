---
title: Iterative Sets Redux
author: nbloomf
date: 2017-04-22
tags: arithmetic-made-difficult
---

Warning: this post is super handwavy!

To recap what we've done so far: we assumed the existence of a set, $\nats$, with a special element $\zero$ and a map $\next : \nats \rightarrow \nats$, and a recursion operator $\natrec{e}{\varphi}$ that allowed us to construct recursive maps from $\nats$. On this basis we were able to show that $\nats$ satisfies the Peano axioms. We were also able to define the "usual" arithmetic on $\nats$ and show that it behaves as expected, and moreover these definitions were made *executable* by implementing $\natrec{\ast}{\ast}$ and some other, auxilliary recursion operators in software. I'm using Haskell here out of convenience, but any language with first-class functions could also work.

This is a nice combination; by working with $\natrec{\ast}{\ast}$ and its friends we can build programs and prove things about them simultaneously. If such things interest you, two questions arise:

1. We assumed the existence of $\nats$. Is there a more fundamental basis or principle we can use to argue that it exists?
2. $\nats$, while useful, is a very special thing. Are there other interesting mathematical or computational objects that can be similarly characterized and reasoned about?

In this post we'll see that the answer to both questions is *yes*. As it turns out, with the right framework we can think of $\nats$ as having been produced by a process of "recursivization", and this process generalizes to produce a vast family of other "structures".

To see how this works let's revisit our old friends the *iterative sets* again, this time from a different perspective. Recall the definition.

:::::: definition ::
A set $A$ with a distinguished element $e$ and a distinguished function $\varphi : A \rightarrow A$ is called an *iterative set*.
::::::::::::::::::::

So an iterative set is (1) a set, with (2) an element, and (3) a function. It turns out we can think of *elements* of sets as *functions* from the one-element set $1 = \{\ast\}$. More precisely, if $e \in A$, we can identify $e$ with the map $e^\prime : 1 \rightarrow A$ given by $e^\prime(\ast) = e$. From now on I'll make this identification implicitly.

So an iterative set is (1) a set $A$, with (2) a map $1 \rightarrow A$, and (3) a map $A \rightarrow A$. We can make this even more succinct. In general, given two mappings $U \rightarrow X$ and $V \rightarrow X$, we can "bundle" them together as a single map $U+V \rightarrow X$. So an alternate definition for iterative sets is the following.

:::::: definition ::
An *iterative set* is a set $A$ with a mapping $\theta : 1+A \rightarrow A$.
::::::::::::::::::::

All we've done here is recast the iterative set data in terms of mappings. And in this language, iterative set homomorphisms have a nice characterization as well:

:::::: definition ::
Let $A$ and $B$ be iterative sets with mappings $\theta_A : 1+A \rightarrow A$ and $\theta_B : 1+B \rightarrow B$. A map $\varphi : A \rightarrow B$ is called an *iterative set homomorphism* if the following diagram commutes.
$$\require{AMScd}
\begin{CD}
1+A @>{1+\varphi}>> 1+B\\
@V{\theta_A}VV @VV{\theta_B}V \\
A @>>{\varphi}> B
\end{CD}$$
::::::::::::::::::::

Let's stick this in our back pocket for now.


Categories and Functors
-----------------------

This series of posts is not really about category theory, but at this point we need a little theory to really understand $\nats$. A *category* is a collection $\mathcal{C}$ of *objects* and *morphisms*, subject to the following rules.

1. To each morphism $f$ we can associate two objects, $\dom(f)$ and $\cod(f)$, called the *domain* and *codomain* of $f$, respectively. If $\dom(f) = A$ and $\cod(f) = B$, we write $f : A \rightarrow B$.
2. If $f$ and $g$ are morphisms and $\dom(g) = \cod(f)$, then there is a morphism $g \circ f$ with $\dom(g \circ f) = \dom(f)$ and $\cod(g \circ f) = \cod(g)$.
3. If $A$ is an object, then there is a morphism $\id_A : A \rightarrow A$ with the property that $\id_A \circ f = f$ when $\cod(f) = A$ and $g \circ \id_A = g$ when $\dom(g) = A$.

I'm being intentionally vague about exactly what "collection" means. For our purposes it doesn't matter too much.

A morphism $f : A \rightarrow B$ is called *left invertible* if there is another morphism $g$ such that $g \circ f = \id_A$, and is called *right invertible* if there is another morphism $h$ such that $f \circ h = \id_B$. If $f$ is both left and right invertible we say it is an *isomorphism*. Two objects which are connected by an isomorphism are, in an abstract sense, indistinguishable from each other.

Categories occasionally contain special objects. For instance, suppose there is an object $X$ with the property that for *every* object $Y$, there is a *unique* morphism $X \rightarrow Y$. If this happens, we say that $X$ is an *initial object*. Analogously, if $X$ is such that there is a unique morphism $Y \rightarrow X$ for any object $Y$, we say that $X$ is a *terminal object*. Initial and terminal objects -- if they exist -- are unique up to isomorphism.

Categories represent a kind of structure. The structure-preserving "maps" are called *functors*, and come in two flavors, called *covariant* and *contravariant*. Given two categories $\mathcal{C}$ and $\mathcal{D}$, a *covariant functor* $F : \mathcal{C} \rightarrow \mathcal{D}$ associates each object $X$ in $\mathcal{C}$ to an object $F(X)$ in $\mathcal{D}$, and each morphism $f : A \rightarrow B$ in $\mathcal{C}$ to a morphism $F(f) : F(A) \rightarrow F(B)$ subject to the following rules.

1. $F(\id_X) = \id_{F(X)}$ for all objects $X$ in $\mathcal{C}$.
2. $F(g \circ f) = F(g) \circ F(f)$ for all morphisms $f$ and $g$ in $\mathcal{C}$ with $\dom(g) = \cod(f)$.

The *contravariant functors* are similar, except that $F$ associates $f : A \rightarrow B$ to $F(f) : F(B) \rightarrow F(A)$ and condition (2) is replaced by

2. $F(g \circ f) = F(f) \circ F(g)$ for all morphisms $f$ and $g$ in $\mathcal{C}$ with $\dom(g) = \cod(f)$.

(Intuitively, covariant functors preserve arrows, while contravariant functors reverse them.) Generally functors "map" between different categories, but lots of interesting functors map one category back to itself. These are called *endofunctors*.

Categories occasionally have some additional internal structure. For example, given two objects $A$ and $B$, a third object $X$ is called their *product* if there exist two maps $\pi_A : X \rightarrow A$ and $\pi_B : X \rightarrow B$ with the property that if we have an object $Z$ and two maps $\varphi_A : Z \rightarrow A$ and $\varphi_B : Z \rightarrow B$, then there is a unique map $\Theta : Z \rightarrow X$ such that $\varphi_A = \pi_A \circ \Theta$ and $\varphi_B = \pi_B \circ \Theta$. That is, a unique $\Theta$ such that the following diagram commutes.
$$\require{AMScd}
\begin{CD}
Z @= Z @= Z\\
@V{\varphi_A}VV @VV{\Theta}V @VV{\varphi_B}V \\
A @<<{\pi_A}< X @>>{\pi_B}> B
\end{CD}$$
If such an object $X$ exists, it is unique up to isomorphism. When this happens -- a thing exists and is unique -- it is useful to introduce notation for it. So the product of $A$ and $B$ (if it exists) is denoted $A \times B$.

There is an analogous concept to the product, called the *coproduct*, obtained by reversing the direction of the arrows. Given objects $A$ and $B$, an object $X$ is called a *coproduct* of $A$ and $B$ if there are morphisms $\iota_A : A \rightarrow X$ and $\iota_B : B \rightarrow X$ such that if $Z$ is an object and $\psi_A : A \rightarrow Z$ and $\psi_B : B \rightarrow Z$ morphisms, there is a unique morphism $\Theta : X \rightarrow Z$ such that $\psi_A = \Theta \circ \iota_A$ and $\psi_B = \Theta \circ \iota_B$. That is, a unique $\Theta$ such that the following diagram commutes.
$$\require{AMScd}
\begin{CD}
A @>{\iota_A}>> X @<{\iota_B}<< B \\
@V{\psi_A}VV @VV{\Theta}V @VV{\psi_B}V \\
Z @= Z @= Z
\end{CD}$$
Again, if such an object $X$ exists, it is unique up to isomorphism. We denote the coproduct of $A$ and $B$ (if it exists) by $A+B$.

Now the "collection" of sets and set functions form a category, and products and coproducts exist between any two sets: the cartesian product and the disjoint sum.

The notation for products and coproducts is suggestive of arithmetic, and indeed $\times$ and $+$ as "operations" on a category enjoy some familiar properties. More germane for us, though, is that they can be used to construct *polynomial endofunctors*. Waving over a bunch of details, we can construct a family endofunctors on a category using the following.

1. The so-called *identity functor* $F$, with $F(X) = X$ and $F(f) = f$ for objects $X$ and morphisms $f$.
2. If $A$ is an object, the so-called *constant functor* $F$ with $F(X) = A$ and $F(f) = \id_A$ for all objects $X$ and morphisms $f$.
3. If $F$ and $G$ are functors, the *product functor* $F \times G$, with $(F \times G)(X) = F(X) \times G(X)$ and $(F \times G)(f) = F(f) \times G(f)$ for all objects $X$ and morphisms $f$.
4. If $F$ and $G$ are functors, the *coproduct functor* $F + G$, with $(F+G)(X) = F(X)+G(X)$ and $(F+G)(f) = F(f)+G(f)$ for all objects $X$ and morphisms $f$.

Functors which are built using a finite number of applications of these production rules are called *polynomial endofunctors*.

Looking back, there appears to be a polynomial endofunctor hidden in our definition of inductive sets.

:::::: definition ::
Let $F$ be the polynomial functor $F(X) = 1+X$. An *iterative set* is a set $A$ with a mapping $\theta_A : F(A) \rightarrow A$.
::::::::::::::::::::

With this example in mind, we make the following definition.

:::::: definition ::
Let $\mathcal{C}$ be a category and $F$ a covariant endofunctor on $\mathcal{C}$. An $F$-algebra is an object $A$ coupled with a morphism $\theta_A : F(A) \rightarrow A$.

Given two $F$-algebras $(A,\theta_A)$ and $(B,\theta_B)$, an $F$-algebra homomorphism is a morphism $\varphi : A \rightarrow B$ such that $F(\varphi) \circ \theta_B = \theta_A \circ \varphi$. That is, a morphism $\varphi$ such that the following diagram commutes.
$$\require{AMScd}
\begin{CD}
F(A) @>{F(\varphi)}>> F(B)\\
@V{\theta_A}VV @VV{\theta_B}V \\
A @>>{\varphi}> B
\end{CD}$$
::::::::::::::::::::

Now it can be shown that the collection of $F$-algebras and $F$-algebra homomorphisms form a category. And now the natural numbers have a very nice characterization.

:::::: definition ::
$\nats$ is the initial $F$-algebra of the functor $F(X) = 1+X$.
::::::::::::::::::::

Recall that an object in a category is called *initial* if there is exactly one morphism from it to any other given object. In the case of $\nats$, the unique morphism is precisely $\natrec{\ast}{\ast}$.

Now I am not too interested at the moment in digging into the conditions under which a given functor *has* an initial algebra; I am happy enough using the existence of an initial algebra as the basis for reasoning about recursively defined programs. So this is as far as I will take this business about categories. We will only be interested in a small handful of concrete polynomial endofunctors, and each time we see one, we will just add an axiom assuming that it has an initial algebra -- as we did with $\nats$.

Now if an initial algebra $A$ exists for $F$, it turns out that this algebra acts like a *fixed point* up to isomorphism -- in fact, the algebra morphism $F(A) \rightarrow A$ is an isomorphism. This will allow us to define $A$ recursively, as we did with $\nats$. One hitch we have to worry about is that the initial algebra of a functor is its *least* fixed point, in the sense that there is a unique "injection" from the least fixed point to any other fixed point. Why is this relevant? It is tricky to impose this minimality condition on a Haskell type. For example, all along we've been implicitly assuming that every element of $\nats$ is somehow "finite" (whatever that means) -- obtained by a finite number of applications of $\next$ to $\zero$. But Haskell will happily typecheck an expression like

```haskell
omega :: Nat
omega = next omega
```

What's going on here is that the ``Nat`` type doesn't quite model $\nats$. By definition it is a fixed point of the functor $F(X) = 1+X$, but it is not the *least* fixed point. (I want to say it is the greatest fixed point, but I'm not sure about that.)

What should we do about this? Certainly this problem will pop up again. There are more powerful type systems that can enforce the minimalness of fixed points, but we'd prefer not to require too much type-fanciness. I think it is enough to simply require that recursion be defined using initial algebra maps like $\natrec{\ast}{\ast}$; this requirement would make a definition like ``omega`` illegal.

So, in summary, given a functor $F$ the $F$-algebras are a family of structures, and the process of constructing an initial algebra for $F$ is a kind of uniform "recursivization". From now on we will define recursive sets simply by assuming that such an initial algebra exists.
