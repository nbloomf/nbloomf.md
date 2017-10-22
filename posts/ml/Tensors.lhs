---
title: Tensors
author: nbloomf
date: 2017-10-14
tags: ml, literate-haskell
---

First some boilerplate.

> {-# LANGUAGE LambdaCase #-}
> module Tensors where
> 
> import Data.Array
> import Data.Foldable
> import Control.Applicative
> import Text.PrettyPrint
> import Test.QuickCheck
> 
> import Indices
> import IndexIsos

In the last post, we defined two algebras whose elements represent the possible sizes of multidimensional arrays and possible indices into multidimensional arrays, respectively. We did this in such a way that the possible indices into an array with (vector space) dimension $k$ can be mapped to $\{0,1, \ldots, k-1\}$ in a canonical way. With this in hand, we can define a <em>tensor</em> of size $s \in \mathbb{S}$ as a mapping from the indices of $s$ to $\mathbb{R}$. And thanks to the canonical mapping to integers, we can implement our tensors in memory using a linear array. In math notation, we will identify each $s \in \mathbb{S}$ with its indices, and think of tensors as elements of $\mathbb{R}^s$ (that is, functions from indices to real numbers).

> data Tensor r = T
>   { size :: Size
>   , elts :: (Array Integer r)
>   }

We'll say that two tensors are <em>strictly equal</em>, denoted ``$==``, if they have the same sizes and the same entries at each index.

> ($==) :: (Eq r) => Tensor r -> Tensor r -> Bool
> a@(T u x) $== b@(T v y) = (u == v) && (x == y)

(Strict equality is too, well, <em>strict</em>. We'll nail down the real equality on tensors in a moment.)

A tensor "is" a map from indices to $\mathbb{R}$s. The ``tensor`` function lets us build a tensor by supplying this map.

> tensor :: Size -> (Index -> r) -> Tensor r
> tensor s f = T s (array (0,(dimOf s)-1) entries)
>   where
>     entries = [(flatten s t, f t) | t <- indicesOf s]

To retrieve the entry of a tensor at a given index, we evaluate the tensor as a function. We'll call this ``at``. So in math notation, we'd write $\mathsf{at}(A,i) = A(i)$ or $A_i$.

> at :: Tensor r -> Index -> r
> at (T s a) t = if t `isIndexOf` s
>   then a ! (flatten s t)
>   else error "incompatible index"

So ``tensor`` and ``at`` obey the following identities:

```haskell
a@(T u _) == tensor u (\i -> a`at`i)

(tensor u f) `at` i == f i
```

We'll also define some helper functions to make building tensors more convenient. For instance, a <em>uniform</em> tensor has the same value at each index.

> uniform :: Size -> r -> Tensor r
> uniform s x = tensor s (\_ -> x)
> 
> ones, zeros :: (Num r) => Size -> Tensor r
> ones s = uniform s 1
> zeros s = uniform s 0

We can use ``at`` and the canonical isomorphism on index sets to define equality for tensors.

> instance (Eq r) => Eq (Tensor r) where
>   a@(T u _) == b@(T v _) = if u ~= v
>     then all (\i -> (a`at`i) == (b`at`(mapIndex u v i))) (indicesOf u)
>     else False

We'll see the reason for this weak equality in a bit. But for now, note that the following two tensors are <em>equal</em>, but not <em>strictly equal</em>.

```haskell
x = ones (2*(2*2)) :: Tensor Int
y = ones ((2*2)*2) :: Tensor Int
```

More generally, strict equality implies equality, but not vice versa.

The simplest possible (nontrivial) tensor has size 1; we will call these <em>cells</em>.

> cell :: r -> Tensor r
> cell r = tensor 1 (\_ -> r)

We'll also provide a simple way to construct vectors with natural number size.

> vec :: [r] -> Tensor r
> vec xs = tensor k (\(Index i) -> xs !! (fromIntegral i))
>   where
>     k = Size $ fromIntegral $ length xs

The downside of defining our tensors recursively is that it's less clear what the index of a given entry is. To help out with this, we'll define two helpers: ``indexOf``, that defines a tensor of a given size whose entries are equal to their indices, and ``orderOf``, that shows how the entries of a tensor are linearized internally.

> indexOf :: Size -> Tensor Index
> indexOf s = tensor s id
> 
> orderOf :: Size -> Tensor Integer
> orderOf s = tensor s (flatten s)

This works because we can pass ``tensor`` <em>any</em> function on indices. For example, here are three different views of a size $3 \otimes 3$ tensor.

```haskell
$> ones (3*3)
1 1 1
1 1 1
1 1 1
$> indexOf (3*3)
(0,0) (0,1) (0,2)
(1,0) (1,1) (1,2)
(2,0) (2,1) (2,2)
$> orderOf (3*3)
0 3 6
1 4 7
2 5 8
```


Tensor as a Functor
-------------------

One of the first questions we ask about type constructors is whether they are naturally members of any interesting classes. It's not too surprising that ``Tensor`` is a functor, where ``fmap`` is "pointwise" function application.

> instance Functor Tensor where
>   fmap f a@(T u _) = tensor u (\i -> f (a`at`i))

To verify the functor laws, we make sure that ``fmap id == id``. (Remember that ``$==`` means strict equality.)

```haskell
    fmap id a
$== fmap id a@(T u _)
$== tensor u (\i -> id (a`at`i))
$== tensor u (\i -> a`at`i)
$== a
```

and that ``fmap (g . f) == fmap g . fmap f``.

```haskell
    fmap g (fmap f a)
$== fmap g (fmap f a@(T u _))
$== fmap g (tensor u (\i -> f (a`at`i)))
$== tensor u (\i -> g ((tensor u (\j -> f (a`at`j))) `at` i))
$== tensor u (\i -> g (f (a`at`i)))
$== tensor u (\i -> (g . f) (a`at`i))
$== fmap (g . f) a
```

We can also define a ``Foldable`` instance for tensors, using the canonical order on indices.

> instance Foldable Tensor where
>   foldMap f a@(T u _)
>     = foldMap f [ a`at`i | i <- indicesOf u ]

From here we can immediately take the ``sum`` and ``maximum`` of a tensor. We'll also define a kind of ``zip`` for tensors of equivalent size; I had trouble finding a good general class for zippable functors in the libraries.

> tzip :: Tensor a -> Tensor b -> Tensor (a,b)
> tzip a@(T u _) b@(T v _) = if u ~= v
>   then tensor u (\i -> (a`at`i, b`at`(mapIndex u v i)))
>   else error "zip: tensors must have equivalent size"
> 
> tzipWith :: (a -> b -> c) -> Tensor a -> Tensor b -> Tensor c
> tzipWith f a b = fmap (uncurry f) $ tzip a b

``Tensor`` is also applicative. (Making this work is the main motivation for defining equality the way we did.)

> instance Applicative Tensor where
>   pure = cell
> 
>   a@(T u _) <*> b@(T v _) = tensor (u :* v) $
>     \(i :& j) -> (a `at` i) (b `at` j)

We need to see that this implementation satisfies the applicative laws. First the identity law:

``pure id <*> a == a`` for all ``a``

```haskell
    pure id <*> a
$== cell id <*> a@(T u _)
$== (tensor 1 (const id)) <*> a@(T u _)
$== tensor (1 :* u) (\(i :& j) -> id (a`at`j))
$== tensor (1 :* u) (\(i :& j) -> a`at`j)
 == tensor u (\j -> a`at`j)
$== a
```

Next we establish the composition law:

``pure (.) <*> a <*> b <*> c == a <*> (b <*> c)``.

```haskell
    pure (.) <*> a <*> b <*> c
$== tensor 1 (const (.)) <*> a@(T u _) <*> b <*> c
$== tensor (1 :* u) (\(i :& j) -> (.) (a`at`j)) <*> b@(T v _) <*> c
$== tensor ((1 :* u) :* v) (\((i :& j) :& k) -> (a`at`j) . (b`at`k)) <*> c@(T w _)
$== tensor (((1 :* u) :* v) :* w) (\(((i :& j) :& k) :& l) -> (a`at`j) . (b`at`k) $ (c`at`l))
 == tensor (u :* (v :* w)) (\(j :& (k :& l)) -> (a`at`j) $ (b`at`k) (c`at`l))
$== a <*> tensor (v :* w) (\(k :& l) -> (b`at`k) (c`at`l))
$== a <*> (b <*> c)
```

The homomorphism law:

``pure f <*> pure x == pure (f x)``

```haskell
    pure f <*> pure x
$== tensor 1 (const f) <*> tensor 1 (const x)
$== tensor (1 :* 1) (\(i :& j) -> f x)
 == tensor 1 (\_ -> f x)
$== pure (f x)
```

And the interchange law:

``a <*> pure x = pure ($ x) <*> a``

```haskell
    a <*> pure x
$== a@(T u _) <*> tensor 1 (const x)
$== tensor (u :* 1) (\(i :& j) -> (a`at`i) x)
 == tensor (1 :* u) (\(j :& i) -> ($ x) (a`at`i))
$== tensor 1 (const ($ x)) <*> a@(T u _)
$== pure ($ x) <*> a
```

It may seem like overkill to go to the trouble of defining equality the way we did just to make ``Tensor`` an applicative functor, and it is -- we won't need the applicativeness much. But there's a payoff: the outer product of tensors is defined in terms of ``<*>``.

While we're at it, ``Tensor`` is also ``Alternative``.

> instance Alternative Tensor where
>   empty = tensor 0 (\_ -> undefined)
> 
>   a@(T u _) <|> b@(T v _) = tensor (u :+ v) $
>     \case
>       L i -> a `at` i
>       R j -> b `at` j

We should also verify the ``Alternative`` laws. First the monoid laws that everyone agrees ``Alternatives`` should satisfy. Left identity:

``empty <|> a == a``

```haskell
    empty <|> a
$== tensor 0 (const undefined) <|> a@(T u _)
$== tensor (0 :+ u) (\case L i -> undefined; R j -> a`at`j)
 == tensor u (\j -> a`at`j)
$== a
```

Right identity:

``a <|> empty == a``

```haskell
    a <|> empty
$== a@(T u _) <|> tensor 0 (const undefined)
$== tensor (u :+ 0) (\case L i -> a`at`i; R j -> undefined)
 == tensor u (\i -> a`at`i)
$== a
```

Associativity:

``(a <|> b) <|> c == a <|> (b <|> c)``

```haskell
    (a <|> b) <|> c
$== (a@(T u _) <|> b@(T v _)) <|> c
$== (tensor (u :+ v) (\case L i -> a`at`i; R j -> b`at`j)) <|> c@(T w _)
$== tensor ((u :+ v) :+ w) (\case L l -> (case l of L i -> a`at`i; R j -> b`at`j)); R k -> c`at`k)
$== tensor ((u :+ v) :+ w) (\case L (L i) -> a`at`i; L (R j) -> b`at`j; R k -> c`at`k)
 == tensor (u :+ (v :+ w)) (\case L i -> a`at`i; R (L j) -> b`at`j; R (R k) -> c`at`k)
$== tensor (u :+ (v :+ w)) (\case L i -> a`at`i; R l -> (case l of L j -> b`at`j; R k -> c`at`k))
$== a <|> tensor (v :+ w) (\case L j -> b`at`j; R m -> c`at`m)
$== a <|> (b <|> c)
```

And some of the laws that only hold for some ``Applicative`` instances (including this one). Left zero:

``empty <*> a == empty``

```haskell
    empty <*> a
$== tensor 0 (const undefined) <*> a@(T u _)
$== tensor (0 :* u) (\(i :& j) -> undefined (a `at` j))
 == tensor 0 (\_ -> undefined)
$== empty
```

Right zero:

``a <*> empty == empty``

```haskell
    a <*> empty
$== a@(T u _) <*> tensor 0 (const undefined)
$== tensor (u :* 0) (\(i :& j) -> (a`at`i) undefined)
 == tensor 0 (\_ -> undefined)
$== empty
```


Vector Arithmetic
-----------------

Tensors are vectors, so they should have the usual vector operations of plus, negate, and scale.

> (.+) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> (.+) = tzipWith (+)
> 
> neg :: (Num r) => Tensor r -> Tensor r
> neg = fmap negate
> 
> (.-) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> a .- b = a .+ (neg b)
> 
> (.@) :: (Num r) => r -> Tensor r -> Tensor r
> r .@ a = fmap (r*) a

The Hadamard or entrywise product is also handy.

> (.*) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> (.*) = tzipWith (*)

Thinking of tensors as vectors, we can dot them together in the usual way.

> dot :: (Num r) => Tensor r -> Tensor r -> r
> dot a b = sum $ a .* b

In math notation, if $A,B \in \mathbb{R}^s$, $$\mathsf{dot}(A,B) = \sum_{i \in s} A_i B_i.$$ The 'dot square' of a tensor will also be handy later.

> normSquared :: (Num r) => Tensor r -> r
> normSquared a = dot a a


Structural Arithmetic
---------------------

Now we'll define some structural operators on tensors; these are functions that manipulate the size of a tensor, or combine tensors into more complicated ones, or extract subparts. First is ``oplus``, which constructs a tensor with sum shape.

> oplus, (⊕) :: Tensor r -> Tensor r -> Tensor r
> oplus = (<|>)
> 
> (⊕) = oplus

In a rough and handwavy way, if $a \in \mathbb{R}^u$ and $b \in \mathbb{R}^v$, then $$a \oplus b \in \mathbb{R}^u \oplus \mathbb{R}^v \cong \mathbb{R}^{u \oplus v},$$ and $\oplus$ is the operator that achieves this isomorphism.

This function ``otimes`` is called the <em>dyadic</em> or <em>outer product</em>.

> otimes, (⊗) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> otimes a b = (*) <$> a <*> b -- omg
> 
> (⊗) = otimes

Next we have projection operators, which take a tensor in $\mathbb{R}^{s \otimes t}$ and fix one of the index components. In the usual matrix language, projection would extract one row or one column of a matrix. There are two of these, with the following signature.

> projR, projL :: Index -> Tensor r -> Tensor r

In math notation we have $\mathsf{projR} : s \rightarrow \mathbb{R}^{t \otimes s} \rightarrow \mathbb{R}^t$ given by $\mathsf{projL}(i,A)_j = A_{i \& j}$, and $\mathsf{projL}$ is similar.

> projR i a@(T (u :* v) _) = if (i `isIndexOf` u)
>   then tensor v (\j -> a `at` (i :& j))
>   else error "projR: index and size not compatible."
> projR _ _ = error "projR: tensor argument must have product shape"
> 
> projL j a@(T (u :* v) _) = if (j `isIndexOf` v)
>   then tensor u (\i -> a `at` (i :& j))
>   else error "projL: index and size not compatible."
> projL _ _ = error "projL: tensor argument must have product shape"

Similarly, we can extract "terms" from a summand tensor using functions with the following signature.

> termL, termR :: Tensor r -> Tensor r

In math notation we have $\mathsf{termL} : \mathbb{R}^{s \oplus t} \rightarrow \mathbb{R}^s$ given by $\mathsf{termL}(A)_i = A_{\mathsf{l}(i)}$, and $\mathsf{termR}$ is similar.

> termL a@(T (u :+ _) _) =
>   tensor u (\i -> a `at` (L i))
> termL _ = error "termL: argument must have sum shape"
> 
> termR a@(T (_ :+ v) _) =
>   tensor v (\j -> a `at` (R j))
> termR _ = error "termR: argument must have sum shape"

Now $\mathbb{R}^{u \otimes v}$ and $\mathbb{R}^{v \otimes u}$ are not equal, but they are canonically isomorphic; likewise $\mathbb{R}^{u \oplus v}$ and $\mathbb{R}^{v \oplus u}$. ``comm`` achieves this.

> comm :: Tensor r -> Tensor r
> 
> comm a@(T (u :* v) _) = tensor (v :* u) $
>   \(j :& i) -> a `at` (i :& j)
> 
> comm a@(T (u :+ v) _) = tensor (v :+ u) $
>   \k -> case k of
>     L i -> a `at` R i
>     R i -> a `at` L i
> 
> comm _ = error "comm"

Similarly, $\mathbb{R}^{u \otimes (v \otimes w)}$ and $\mathbb{R}^{(u \otimes v) \otimes w}$ are canonically isomorphic, and likewise for $\oplus$.

> assocL, assocR :: Tensor r -> Tensor r
> 
> assocL a@(T (u :* (v :* w)) _) = tensor ((u :* v) :* w) $
>   \((i :& j) :& k) -> a `at` (i :& (j :& k))
> 
> assocL a@(T (u :+ (v :+ w)) _) = tensor ((u :+ v) :+ w) $
>   \k -> case k of
>     L (L i) -> a `at` L i
>     L (R i) -> a `at` R (L i)
>     R i     -> a `at` R (R i)
> 
> assocL _ = error "assocL: argument has wrong shape"
> 
> assocR a@(T ((u :* v) :* w) _) = tensor (u :* (v :* w)) $
>   \(i :& (j :& k)) -> a `at` ((i :& j) :& k)
> 
> assocR a@(T ((u :+ v) :+ w) _) = tensor (u :+ (v :+ w)) $
>   \k -> case k of
>     R (R i) -> a `at` R i
>     R (L i) -> a `at` L (R i)
>     L i     -> a `at` L (L i)
> 
> assocR _ = error "assocR: argument has wrong shape"

Recall that the $\otimes$ operator in $\mathbb{S}$ does not really distribute over $\oplus$, so for example $a \otimes (b \oplus c)$ and $(a \otimes b) \oplus (a \otimes c)$ are distinct tensor sizes, and meanwhile we have $$\mathbb{R}^{(a \otimes b) \oplus (a \otimes c)} \cong \mathbb{R}^{a \otimes b} \times \mathbb{R}^{a \otimes c}.$$ We'll define a couple of operators to canonically "undistribute" $\otimes$ over $\oplus$.

> unDistL, (~-~) :: Tensor r -> Tensor r -> Tensor r
> unDistL a@(T (u :* h) _) b@(T (v :* k) _) =
>   if h == k
>     then tensor ((u :+ v) :* k)
>       (\ (t :& k) -> case t of
>         L i -> a `at` (i :& k)
>         R j -> b `at` (j :& k)
>       )
>     else error "size mismatch"
> 
> (~-~) = unDistL
> 
> unDistR, (~|~) :: Tensor r -> Tensor r -> Tensor r
> unDistR a@(T (h :* u) _) b@(T (k :* v) _) =
>   if h == k
>     then tensor (k :* (u :+ v))
>       (\ (k :& t) -> case t of
>         L i -> a `at` (k :& i)
>         R j -> b `at` (k :& j)
>       )
>     else error "size mismatch"
> 
> (~|~) = unDistR

We give ``unDistL`` and ``unDistR`` symbolic synonyms, meant to evoke what they do on matrices. ``unDistL`` concatenates matrices vertically, and ``unDistR`` concatenates them horizontally.

The last "structural" operations on tensors (at least for now) will be a kind of "map" on sum tensors and a "fold" on product tensors. For sum sizes:

> mapTermL :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> mapTermL f a@(T (u :+ v) _) =
>   let
>     m = f (termL a)
>     w = size m
>   in
>     tensor (w :+ v) $
>       \k -> case k of
>         L i -> m `at` i
>         R i -> a `at` (R i)
> mapTermL _ _ = error "mapTermL: tensor argument must have sum shape"
> 
> mapTermR :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> mapTermR f a@(T (u :+ v) _) =
>   let
>     m = f (termR a)
>     w = size m
>   in
>     tensor (w :+ v) $
>       \k -> case k of
>         R i -> m `at` i
>         L i -> a `at` (L i)
> mapTermR _ _ = error "mapTermR: tensor argument must have sum shape"

And for product sizes:

> foldFactorL :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> foldFactorL f a@(T (u :* v) _) = tensor (w :* v) $
>   \(i :& j) -> f (projL j a) `at` i
>   where
>     w = case common [ size $ f (projL j a) | j <- indicesOf v ] of
>       Just k -> k
>       Nothing -> error "foldFactorL: function must be well-defined on size"
> foldFactorL _ _ = error "foldFactorL: tensor argument must have product shape"
> 
> foldFactorR :: (Tensor r -> Tensor r) -> Tensor r -> Tensor r
> foldFactorR f a@(T (u :* v) _) = tensor (u :* w) $
>   \(i :& j) -> f (projR i a) `at` j
>   where
>     w = case common [ size $ f (projR i a) | i <- indicesOf u ] of
>       Just k -> k
>       Nothing -> error "foldFactorR: function must be well-defined on size"
> foldFactorR _ _ = error "foldFactorR: tensor argument must have product shape"
> 
> common :: (Eq a) => [a] -> Maybe a
> common []     = Nothing
> common (x:xs) = if not $ any (/= x) xs
>   then Just x
>   else Nothing

As an example, given a matrix we can use the ``foldFactor`` operators to sum the rows or columns.

> sumRows, sumCols :: (Num r) => Tensor r -> Tensor r
> sumRows = foldFactorR (cell . sum)
> sumCols = foldFactorL (cell . sum)

Note that ``mapTerm`` and ``foldFactor`` can be nested to manipulate more complicated tensor sizes. For example,

```haskell
foldFactorR (foldFactorR (cell . sum))
```

takes a "three dimensional" tensor and sums along one of the dimensions.


Matrix Operations
-----------------

Now for a couple of matrix-specific operations. First the identity matrix.

> idMat :: (Num r) => Size -> Tensor r
> idMat n = tensor (n :* n) (\ (i :& j) -> if i==j then 1 else 0)

The tensor generalization of matrix multiplication is sometimes called <em>contraction</em>. I'll do the worst possible thing here by using the word "contraction" to refer only to matrix multiplication.

> contract :: (Num r) => Tensor r -> Tensor r -> Tensor r
> contract a@(T (m :* n) _) b@(T (u :* v) _) =
>   if u == n
>     then tensor (m*v)
>       (\ (i :& j) -> sum
>         [ (a`at`(i :& k))*(b`at`(k :& j)) | k <- indicesOf n ])
>     else error "inner sizes must match."
> contract _ _ = error "contraction expects matrices with product sizes."

``contract`` is a generalized matrix multiplication, but it's a little too general. For instance, in linear algebra we sometimes like to multiply an $m \times n$ matrix by an $n$ vector to get an $m$ vector; but using contraction this only really works if we think of the input vector as an $n \times 1$ matrix and the output as a $m \times 1$ matrix. We'll fix this by defining a specialized version of ``contract`` called ``collapse``. If $a \in \mathbb{R}^{m \otimes n}$ and $b \in \mathbb{R}^n$, then $$\mathsf{collapse}(a,b)_i = \sum_{k \in m} a_{i \& k} b_k.$$

> collapse :: (Num r) => Tensor r -> Tensor r -> Tensor r
> collapse a@(T (m :* n) _) b@(T u _) =
>   if u == n
>     then tensor m
>       (\i -> sum
>         [ (a`at`(i :& k))*(b`at`k) | k <- indicesOf n ])
>     else error "collapse: inner sizes must match."
> collapse _ _ = error "collapse: sizes of wrong shape."

> collapseL :: (Num r) => Tensor r -> Tensor r -> Tensor r
> collapseL a@(T u _) b@(T (n :* m) _) =
>   if u == n
>     then tensor m
>       (\i -> sum
>         [ (a`at`k)*(b`at`(k :& i)) | k <- indicesOf n ])
>     else error "collapseL: inner sizes must match."
> collapseL _ _ = error "collapse: sizes of wrong shape."


Pretty Printing
---------------

We'll end this post with the ``Show`` instance for tensors; we'll build it on top of the pretty printing [combinator library](https://hackage.haskell.org/package/pretty-1.1.3.5) by John Hughes and Simon Peyton Jones. (The original [paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.38.8777) on that library is a nice case study in DSL design.)

First we convert a tensor of strings to a ``Doc`` (in the pretty printer parlance), doing more or less the obvious thing.

> toDoc :: Tensor String -> Doc
> toDoc a@(T s _) =
>   case s of
>     Size k -> hsep $ map text [ a`at`i | i <- indicesOf s ]
>     u :+ v -> (toDoc $ termL a) $$ (toDoc $ termR a)
>     u :* v -> vcat [
>                 hsep [
>                   text $ a `at` (i :& j)
>                 | j <- indicesOf v ]
>               | i <- indicesOf u ]

To actually show the tensor, we show the entries (pointwise) and pad to the maximum entry width (so the cells line up), then show the corresponding ``Doc``.

> instance (Show r) => Show (Tensor r) where
>   show a =
>     let
>       cellWidth = maximum $ fmap (length . show) a
>       m = fmap (padLeft cellWidth . show) a
>     in
>       ":" ++ (show $ size m) ++ ":\n" ++
>       (render $ toDoc m)
>     where
>       -- left-pad a string with spaces to a given length
>       padLeft :: Int -> String -> String
>       padLeft k = reverse . take k . (++ (repeat ' ')) . reverse

This method for displaying tensors is not perfect, but it has the advantage of being simple and doing mostly the right thing in the most common cases of $k$ and $m \otimes n$ tensors (i.e. matrices). Apropos of nothing: further support for this method is that tensors with shape $k_1 \oplus k_2 \oplus \cdots \oplus k_n$ look like [Young tableaux](https://en.wikipedia.org/wiki/Young_tableau).


Tests
-----

In future posts we'll be writing tests involving tensors, so I'll put an ``Arbitrary`` instance here.

> instance (Arbitrary r) => Arbitrary (Tensor r) where
>   arbitrary = arbitrary >>= arbTensor
> 
>   shrink a@(T u _) = case u of
>     Size k ->
>       if k <= 0
>         then []
>         else
>           [ tensor (Size $ k-1) (\i -> a`at`i)
>           , uniform (Size $ k-1) (a`at`0)
>           ]
> 
>     _ :+ _ -> concat
>       [ [ h <|> k | h <- shrink $ termL a, k <- shrink $ termR a ]
>       , [ termL a, termR a ]
>       ]
> 
>     _ -> []
> 
> arbTensor :: (Arbitrary r) => Size -> Gen (Tensor r)
> arbTensor s = do
>   as <- vectorOf (fromIntegral $ dimOf s) arbitrary
>   return $ tensor s (\i -> as !! (fromIntegral $ flatten s i))
> 
> arbMatrix :: (Arbitrary r) => Integer -> Integer -> Gen (Tensor r)
> arbMatrix r c = arbTensor ((Size r) :* (Size c))
