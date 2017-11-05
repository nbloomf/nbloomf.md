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
> import qualified Text.PrettyPrint as PP
> import Test.QuickCheck
> 
> import Indices
> import IndexIsos

[Earlier](/posts/ml/Indices.html), we defined two algebras whose elements represent the possible sizes of multidimensional arrays and possible indices into multidimensional arrays, respectively. We did this in such a way that the possible indices into an array with (vector space) dimension $k$ can be mapped to $\{0,1, \ldots, k-1\}$ in a canonical way. With this in hand, we can define a <em>tensor</em> of size $s \in \mathbb{S}$ as a mapping from the indices of $s$ to $\mathbb{R}$. And thanks to the canonical mapping to integers, we can implement our tensors in memory using a linear array. In math notation, we will identify each $s \in \mathbb{S}$ with its indices, and think of tensors as elements of $\mathbb{R}^s$ (that is, functions from indices to real numbers).

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

We're actually going to define two slightly different versions of ``at``. The first works only on nonzero sizes, but for all entry types. The second treats the size zero vector as if it has entry 0 at every possible index, but of course only makes sense for numeric entry types. (Looking ahead, there's a good reason for doing this, having to do with dual numbers and automatic differentiation.)

> at' :: Tensor r -> Index -> r
> at' (T s a) t = if t `isIndexOf` s
>   then a ! (flatten s t)
>   else error $ "at: incompatible index " ++ show t
>     ++ " for size " ++ show s
> 
> at :: (Num r) => Tensor r -> Index -> r
> at a t =
>   if (size a) ~= 0
>     then 0
>     else a `at'` t

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

We'll use the notation $\mathsf{Zero}_s$ to denote the zero tensor of size $s$.

We can use ``at`` and the canonical isomorphism on index sets to define equality for tensors.

> instance (Eq r) => Eq (Tensor r) where
>   a@(T u _) == b@(T v _) = if u ~= v
>     then all (\i -> (a`at'`i) == (b`at'`(mapIndex u v i))) (indicesOf u)
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

We'll also provide a simple way to construct vectors and matrices with natural number size.

> vec :: [r] -> Tensor r
> vec xs = tensor k (\(Index i) -> xs !! (fromIntegral i))
>   where
>     k = Size $ fromIntegral $ length xs
> 
> mat :: [[r]] -> Tensor r
> mat []   = tensor 0 (const undefined)
> mat [[]] = tensor 0 (const undefined)
> mat xss  = tensor (r :* c) $
>   \((Index i) :& (Index j))
>     -> (xss !! (fromIntegral i)) !! (fromIntegral j)
>   where
>     r = Size $ fromIntegral $ length xss
>     c = Size $ fromIntegral $ length $ head xss

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

Try using ``indexOf`` on more complicated sizes.


Tensor as a Functor
-------------------

One of the first questions we ask about type constructors is whether they are naturally members of any interesting classes. It's not too surprising that ``Tensor`` is a functor, where ``fmap`` is "pointwise" function application.

> instance Functor Tensor where
>   fmap f a@(T u _) = tensor u (\i -> f (a`at'`i))

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
>     = foldMap f [ a`at'`i | i <- indicesOf u ]

From here we can immediately take the ``sum`` and ``maximum`` of a tensor. We'll also define a kind of ``zip`` for tensors of equivalent size; I had trouble finding a good general class for zippable functors in the libraries.

> tzip :: Tensor a -> Tensor b -> Tensor (a,b)
> tzip a@(T u _) b@(T v _) = if u ~= v
>   then tensor u (\i -> (a`at'`i, b`at'`(mapIndex u v i)))
>   else error "zip: tensors must have equivalent size"
> 
> tzipWith :: (a -> b -> c) -> Tensor a -> Tensor b -> Tensor c
> tzipWith f a b = fmap (uncurry f) $ tzip a b

``Tensor`` is also applicative. (Making this work is the main motivation for defining equality the way we did.)

> instance Applicative Tensor where
>   pure = cell
> 
>   a@(T u _) <*> b@(T v _) = tensor (u :* v) $
>     \(i :& j) -> (a `at'` i) (b `at'` j)

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
$== tensor (1 :* u) (\(i :& j) -> (.) (a`at`j))
      <*> b@(T v _) <*> c
$== tensor ((1 :* u) :* v)
      (\((i :& j) :& k) -> (a`at`j) . (b`at`k))
      <*> c@(T w _)
$== tensor (((1 :* u) :* v) :* w)
      (\(((i :& j) :& k) :& l) ->
        (a`at`j) . (b`at`k) $ (c`at`l))
 == tensor (u :* (v :* w))
      (\(j :& (k :& l)) -> (a`at`j) $ (b`at`k) (c`at`l))
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
>       L i -> a `at'` i
>       R j -> b `at'` j

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
$== (tensor (u :+ v)
      (\case
        L i -> a`at`i
        R j -> b`at`j
      )) <|> c@(T w _)
$== tensor ((u :+ v) :+ w)
      (\case
        L l -> case l of
          L i -> a`at`i
          R j -> b`at`j
        R k -> c`at`k)
$== tensor ((u :+ v) :+ w)
      (\case
        L (L i) -> a`at`i
        L (R j) -> b`at`j
        R k -> c`at`k)
 == tensor (u :+ (v :+ w))
      (\case
        L i -> a`at`i
        R (L j) -> b`at`j
        R (R k) -> c`at`k)
$== tensor (u :+ (v :+ w))
      (\case
        L i -> a`at`i
        R l -> case l of
          L j -> b`at`j
          R k -> c`at`k))
$== a <|> tensor (v :+ w)
      (\case
        L j -> b`at`j
        R m -> c`at`m)
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

Tensors are vectors, so they should have the usual vector operations of plus, negate, and scale. Other vector spaces will show up later, so we'll define these operations with a class.

> class Vector t where
>   (.@) :: (Num r) => r -> t r -> t r
>   (.+) :: (Num r) => t r -> t r -> t r
>   neg :: (Num r) => t r -> t r
> 
>   (.-) :: (Num r) => t r -> t r -> t r
>   a .- b = a .+ (neg b)
> 
>   vsum :: (Num r) => [t r] -> t r
>   vsum = foldr1 (.+)
> 
> 
> instance Vector Tensor where
>   r .@ a = fmap (r*) a
> 
>   a .+ b
>     | size a ~= 0 = b
>     | size b ~= 0 = a
>     | otherwise   = tzipWith (+) a b
> 
>   neg = fmap negate

The Hadamard or entrywise product is also handy. While we're at it, entrywise quotients.

> (.*) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> (.*) = tzipWith (*)
> 
> (./) :: (Num r, Fractional r) => Tensor r -> Tensor r -> Tensor r
> (./) = tzipWith (/)

Thinking of tensors as vectors, we can dot them together in the usual way.

> dot :: (Num r) => Tensor r -> Tensor r -> r
> dot a b = sum $ a .* b

In math notation, if $A,B \in \mathbb{R}^s$, $$\mathsf{dot}(A,B) = \sum_{i \in s} A_i B_i.$$ The 'dot square' of a tensor will also be handy later.

> normSquared :: (Num r) => Tensor r -> r
> normSquared a = dot a a

We also have some tensor-centric operations. First is ``oplus``, which constructs a tensor with sum shape.

> oplus, (⊕) :: Tensor r -> Tensor r -> Tensor r
> oplus = (<|>)
> 
> (⊕) = oplus

In a rough and handwavy way, if $a \in \mathbb{R}^u$ and $b \in \mathbb{R}^v$, then $$a \oplus b \in \mathbb{R}^u \oplus \mathbb{R}^v \cong \mathbb{R}^{u \oplus v},$$ and $\oplus$ is the operator that achieves this isomorphism.

This function ``otimes`` is called the <em>dyadic</em> or <em>outer product</em>.

> otimes, (⊗) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> otimes = liftA2 (*) -- omg
> 
> (⊗) = otimes


Structural Arithmetic
---------------------

Now we'll define some structural operators on tensors; these are functions that manipulate the size of a tensor, or combine tensors into more complicated ones, or extract subparts. These are mostly based on ``extract``, which defines a new tensor in terms of an existing one.

> extract :: Size -> (Index -> Index) -> Tensor r -> Tensor r
> extract u f a = tensor u (\i -> a `at'` (f i))

For example, we can extract "terms" from a summand tensor using ``extract`` like so.

> termL, termR :: Tensor r -> Tensor r
> 
> termL a@(T (u :+ _) _) = extract u L a
> termL _ = error "termL: argument must have sum shape"
> 
> termR a@(T (_ :+ v) _) = extract v R a
> termR _ = error "termR: argument must have sum shape"

In math notation we have $\mathsf{termL} : \mathbb{R}^{s \oplus t} \rightarrow \mathbb{R}^s$ given by $\mathsf{termL}(A)_i = A_{\mathsf{l}(i)}$, and $\mathsf{termR}$ is similar.

Next we have projection operators, which take a tensor in $\mathbb{R}^{s \otimes t}$ and fix one of the index components. In the usual matrix language, projection would extract one row or one column of a matrix. There are two of these, with the following signature.

> projR, projL :: Index -> Tensor r -> Tensor r
> 
> projR i a@(T (u :* v) _) = if (i `isIndexOf` u)
>   then extract v (i :&) a
>   else error "projR: index and size not compatible."
> projR _ _ = error "projR: tensor argument must have product shape"
> 
> projL j a@(T (u :* v) _) = if (j `isIndexOf` v)
>   then extract u (:& j) a
>   else error "projL: index and size not compatible."
> projL _ _ = error "projL: tensor argument must have product shape"

In math notation we have $\mathsf{projR} : s \rightarrow \mathbb{R}^{t \otimes s} \rightarrow \mathbb{R}^t$ given by $\mathsf{projL}(i,A)_j = A_{i \& j}$, and $\mathsf{projL}$ is similar.

Now $\mathbb{R}^{u \otimes v}$ and $\mathbb{R}^{v \otimes u}$ are not equal, but they are canonically isomorphic; likewise $\mathbb{R}^{u \oplus v}$ and $\mathbb{R}^{v \oplus u}$. ``comm`` achieves this.

> comm :: Tensor r -> Tensor r
> 
> comm a@(T (u :* v) _) =
>   extract (v :* u) f a
>   where
>     f (j :& i) = (i :& j)
> 
> comm a@(T (u :+ v) _) =
>   extract (v :+ u) (opIndex PlusComm) a
> 
> comm _ = error "comm: wrong shape"

Similarly, $\mathbb{R}^{u \otimes (v \otimes w)}$ and $\mathbb{R}^{(u \otimes v) \otimes w}$ are canonically isomorphic, and likewise for $\oplus$.

> assocL, assocR :: Tensor r -> Tensor r
> 
> assocL a@(T (u :* (v :* w)) _) =
>   extract ((u :* v) :* w) (opIndex TimesAssocR) a
> 
> assocL a@(T (u :+ (v :+ w)) _) =
>   extract ((u :+ v) :+ w) (opIndex PlusAssocR) a
> 
> assocL _ = error "assocL: argument has wrong shape"
> 
> 
> assocR a@(T ((u :* v) :* w) _) =
>   extract (u :* (v :* w)) (opIndex TimesAssocL) a
> 
> assocR a@(T ((u :+ v) :+ w) _) =
>   extract (u :+ (v :+ w)) (opIndex PlusAssocL) a
> 
> assocR _ = error "assocR: argument has wrong shape"

We also have $$\mathbb{R}^{(a \otimes b) \oplus (a \otimes c)} \cong \mathbb{R}^{a \otimes b} \times \mathbb{R}^{a \otimes c}.$$ We'll define a couple of operators to canonically "undistribute" $\otimes$ over $\oplus$.

> vcat, (~-~) :: Tensor r -> Tensor r -> Tensor r
> vcat a@(T (u :* h) _) b@(T (v :* k) _) =
>   if h == k
>     then extract ((u :+ v) :* k) (opIndex DistR) (oplus a b)
>     else error "vcat: size mismatch"
> vcat a b = error $ "vcat: sizes with wrong shape: " ++ show (size a)
>   ++ " and " ++ show (size b)
> 
> (~-~) = vcat
> 
> 
> hcat, (~|~) :: Tensor r -> Tensor r -> Tensor r
> hcat a@(T (h :* u) _) b@(T (k :* v) _) =
>   if h == k
>     then extract (k :* (u :+ v)) (opIndex DistL) (oplus a b)
>     else error "hcat: size mismatch"
> 
> (~|~) = hcat

We give ``vcat`` and ``hcat`` symbolic synonyms, meant to evoke what they do on matrices. ``vcat`` concatenates matrices vertically, and ``hcat`` concatenates them horizontally.


Matrix Operations
-----------------

Now for a couple of matrix-specific operations. First the identity matrix.

> idMat :: (Num r) => Size -> Tensor r
> idMat n = tensor (n :* n) (\ (i :& j) -> kronecker i j)

where ``kronecker`` representes the Kronecker delta function $$\delta_{i,j} = \left\{ \begin{array}{ll} 1 & \mathrm{if}\ i = j \\ 0 & \mathrm{otherwise}. \end{array} \right.$$

> kronecker :: (Eq a, Num r) => a -> a -> r
> kronecker x y = if x == y then 1 else 0

And we can "diagonalize" any tensor.

> diag :: (Num r) => Tensor r -> Tensor r
> diag a@(T u _) = tensor (u :* u) $
>   \(i :& j) -> (kronecker i j) * (a`at`i)

The tensor generalization of matrix multiplication is sometimes called <em>contraction</em>. We'll mostly be interested in plain matrix multiplication. We'll define it as a matrix-matrix operation, a matrix-vector operation, and a vector-matrix operation using slightly different symbols. Surely this won't come back to haunt us.

> (***) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> a@(T (m :* n) _) *** b@(T (u :* v) _) =
>   if u == n
>     then tensor (m*v)
>       (\ (i :& j) -> sum
>         [ (a`at`(i :& k))*(b`at`(k :& j)) | k <- indicesOf n ])
>     else error "(***): inner sizes must match."
> _ *** _ = error "(***): expected mat/mat."
> 
> (**>) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> a@(T (m :* n) _) **> b@(T u _) =
>   if u == n
>     then tensor m
>       (\i -> sum
>         [ (a`at`(i :& k))*(b`at`k) | k <- indicesOf n ])
>     else error "(**>): inner sizes must match."
> _ **> _ = error "(**>): expected mat/vec."
> 
> (<**) :: (Num r) => Tensor r -> Tensor r -> Tensor r
> a@(T u _) <** b@(T (n :* m) _) =
>   if u == n
>     then tensor m
>       (\i -> sum
>         [ (a`at`k)*(b`at`(k :& i)) | k <- indicesOf n ])
>     else error "(<**): inner sizes must match."
> _ <** _ = error "(<**): expected vec/mat."


Pretty Printing
---------------

We'll end this post with the ``Show`` instance for tensors; we'll build it on top of the pretty printing [combinator library](https://hackage.haskell.org/package/pretty-1.1.3.5) by John Hughes and Simon Peyton Jones. (The original [paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.38.8777) on that library is a nice case study in DSL design.)

First we convert a tensor of strings to a ``Doc`` (in the pretty printer parlance), doing more or less the obvious thing.

> toDoc :: Tensor String -> PP.Doc
> toDoc a@(T s _) =
>   case s of
>     Size k -> PP.hsep $ map PP.text [ a`at'`i | i <- indicesOf s ]
>     u :+ v -> (toDoc $ termL a) PP.$$ (toDoc $ termR a)
>     u :* v -> PP.vcat [
>                 PP.hsep [
>                   PP.text $ a `at'` (i :& j)
>                 | j <- indicesOf v ]
>               | i <- indicesOf u ]

To actually show the tensor, we show the entries (pointwise) and pad to the maximum entry width (so the cells line up), then show the corresponding ``Doc``.

> instance (Show r) => Show (Tensor r) where
>   show a =
>     let
>       cellWidth = maximum $ fmap (length . show) a
>       m = fmap (padLeft cellWidth . show) a
>     in
>       PP.render $ toDoc m
>     where
>       -- left-pad a string with spaces to a given length
>       padLeft :: Int -> String -> String
>       padLeft k = reverse . take k . (++ (repeat ' ')) . reverse

This method for displaying tensors is not perfect, but it has the advantage of being simple and doing mostly the right thing in the most common cases of $k$ and $m \otimes n$ tensors (i.e. vectors and matrices). Apropos of nothing: further support for this method is that tensors with shape $k_1 \oplus k_2 \oplus \cdots \oplus k_n$ look like [Young tableaux](https://en.wikipedia.org/wiki/Young_tableau).


Tests
-----

In future posts we'll be writing tests involving tensors, so I'll put an ``Arbitrary`` instance here.

> instance (Arbitrary r) => Arbitrary (Tensor r) where
>   arbitrary = arbitrary >>= (arbTensorOf undefined)
> 
>   shrink a@(T u _) = case u of
>     Size k ->
>       if k <= 0
>         then []
>         else
>           [ tensor (Size $ k-1) (\i -> a`at'`i)
>           , uniform (Size $ k-1) (a`at'`0)
>           ]
> 
>     _ :+ _ -> concat
>       [ [ h <|> k | h <- shrink $ termL a, k <- shrink $ termR a ]
>       , [ termL a, termR a ]
>       ]
> 
>     _ -> []
> 
> arbTensorOf :: (Arbitrary r) => r -> Size -> Gen (Tensor r)
> arbTensorOf _ s = do
>   as <- vectorOf (fromIntegral $ dimOf s) arbitrary
>   return $ tensor s (\i -> as !! (fromIntegral $ flatten s i))
