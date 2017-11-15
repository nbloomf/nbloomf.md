---
title: Sizes and Indices
author: nbloomf
date: 2017-10-12
tags: ml, literate-haskell
---

First some boilerplate.

> {-# LANGUAGE LambdaCase #-}
> module Indices where
> 
> import Data.List
> import Test.QuickCheck
> import Test.QuickCheck.Test
> import System.Exit

This post is just some preliminary ideas about tensors - nothing learning-specific yet.

Fundamentally, supervised learning models are (nonlinear) functions involving vector spaces over $\mathbb{R}$. A lot of literature refers to the elements of these spaces as "tensors", because, well, that's what they are. But I think this word "tensor" can be unhelpful in this context for several reasons. For one thing, the correct answer to the question "what is a tensor?" quickly veers into multilinear functions and massive quotient spaces and universal properties and omg I just wanted to write a program to tell the difference between cats and dogs. So I'll just say that a tensor "is" just a multidimensional array, in the sense that a linear transformation "is" a matrix, since for the most part we really want to think of tensors as data, and don't care so much about the  more abstract bits.

With that said, what exactly is a multidimensional array? One definition is that it's an element of a set like $$\mathbb{R}^{k_1 \times k_2 \times \cdots \times k_t}$$ where each $k_t$ is a natural number. And this is totally appropriate. But I am going to do something a little different. I'm not really comfortable defining things in terms of ellipses; that "dot dot dot" hides enough details to make rigorous calculations awkward to my taste. And since from a machine learning perspective we don't really need the full power of tensor algebra, I suspect we can afford to take a different tack.

Instead, let's think for a minute about what we want out of a *multidimensional* array. An array is a really simple kind of data structure, consisting of entries that are accessed using their index or position in the array. That word <em>dimension</em> is a funny thing - what does it really mean here? In the strictest sense, it measures the number of "coordinates" needed to specify an entry in the array. So, for example, an array in $\mathbb{R}^{2 \times 3 \times 4}$ has "dimension" 3, since each entry has an address along 3 different "axes". But then $\mathbb{R}^{5 \times 6 \times 7}$ also has dimension 3 in this sense. (In tensor language we'd call this the "rank" rather than dimension.)

The reason why we attach numbers to things is typically to quantify how alike they are. So: how are arrays in $\mathbb{R}^{2 \times 3 \times 4}$ and $\mathbb{R}^{5 \times 6 \times 7}$ alike? Are they alike enough to warrant using a hefty word like *dimension* to express their similarity, especially when there's a more relevant notion of vector space dimension floating around? I don't think so.

In this post I'll define a couple of algebras in an attempt to nail down a useful notion of <em>shape</em>, <em>size</em>, <em>dimension</em>, and <em>index</em> for multidimensional arrays. For now, when I say <em>algebra</em> I mean <em>universal algebra</em>; that is, a set with some functions on it that satisfy 0 or more universally quantified axioms.

Let's think again about that vector dimension $2 \times 3 \times 4$. This is a funny way to write a dimension. Yes, we can think of a natural number as the set of numbers less than itself, and that $\times$ like the cartesian product of sets, and then $\mathbb{R}^{2 \times 3 \times 4}$ can be thought of as a literal set of functions from the set $2 \times 3 \times 4$ to $\mathbb{R}$, as the notation suggests. But that $2 \times 3 \times 4$ makes it look like we want to express some kind of arithmetic that remembers where it came from, in the sense that $2 \times 3$ and $3 \times 2$ are different. Doing this with actual sets is a little awkward, though, so lets make an algebra instead.

<div class="result">
<div class="defn">
<p>We denote by $\mathbb{S}$ the free algebra over $\mathbb{N}$ with two function symbols of arity 2, denoted $\oplus$ and $\otimes$. Elements of $\mathbb{S}$ are called <em>sizes</em>, and we'll sometimes refer to $\mathbb{S}$ as the <em>algebra of sizes</em>.</p>
</div>
</div>

For example, $2 \oplus 4$ and $5 \otimes (3 \oplus 6)$ are elements of $\mathbb{S}$. Eventually we'll use, for instance, the element $2 \otimes 3$ to describe the "size" of a $2 \times 3$ matrix. The size algebra has no axioms, so for example $a \otimes (b \otimes c)$ and $(a \otimes b) \otimes c$ are not equal. And just ignore the $\oplus$ for now. :)

So the elements of $\mathbb{S}$ look like unevaluated arithmetic expressions with plus and times. By the way, one benefit of using free algebras is we can implement them in Haskell with algebraic data types.

> data Size
>   = Size Integer
>   | Size :+ Size
>   | Size :* Size
>   deriving Eq
> 
> instance Show Size where
>   show =
>     let
>       p x = if ' ' `elem` x
>         then "(" ++ x ++ ")" else x
>     in
>       \case
>         Size k -> show k
>         a :+ b -> concat [p $ show a, " + ", p $ show b]
>         a :* b -> concat [p $ show a, " x ", p $ show b]
> 
> -- so we can define them with numeric literals
> instance Num Size where
>   fromInteger k = if k >= 0
>     then Size k
>     else error "sizes cannot be negative."
>   (+) = (:+)
>   (*) = (:*)
> 
>   abs    = error "Size Num instance: abs makes no sense."
>   signum = error "Size Num instance: signum makes no sense."
>   negate = error "Size Num instance: negate makes no sense."

If you're following along with GHCi, try defining some ``Size``s. (The ``Num`` instance is just there to make the notation less awkward.)

```haskell
$> 4 :: Size
$> 2*3 :: Size
$> 2+(3*4) :: Size
```

Another nice thing about free algebras is that we get universal mappings for free! For example:

<div class="result">
<div class="defn">
<p>We denote by $\mathbb{H}$ the free algebra over $\ast = \{\ast\}$ with two function symbols of arity 2, denoted $\oplus$ and $\otimes$. Elements of $\mathbb{H}$ are called <em>shapes</em>, and we'll sometimes refer to $\mathbb{H}$ as the <em>algebra of shapes</em>. Define $h : \mathbb{N} \rightarrow \ast$ by $h(k) = \ast$, and let $H : \mathbb{S} \rightarrow \mathbb{H}$ be the map induced by $h$. If $s \in \mathbb{S}$, we say $H(s)$ is the <em>shape</em> of $s$.</p>

<p>Note that $(\mathbb{N},+,\times)$ is an algebra with two function symbols of arity 2. Let $D : \mathbb{S} \rightarrow \mathbb{N}$ be the map induced by the identity function on $\mathbb{N}$. If $s \in \mathbb{S}$, we say $D(s)$ is the <em>dimension</em> of $s$.</p>
</div>
</div>

Again, we can implement these in code in the usual way.

> data Shape
>   = HAtom
>   | HPlus Shape Shape
>   | HTimes Shape Shape
>   deriving Eq
> 
> instance Show Shape where
>   show = \case
>     HAtom      -> "*"
>     HPlus  a b -> concat ["(", show a, " + ", show b, ")"]
>     HTimes a b -> concat ["(", show a, " x ", show b, ")"]
> 
> shapeOf :: Size -> Shape
> shapeOf = \case
>   Size _ -> HAtom
>   a :+ b -> HPlus  (shapeOf a) (shapeOf b)
>   a :* b -> HTimes (shapeOf a) (shapeOf b)
> 
> dimOf :: Size -> Integer
> dimOf = \case
>   Size k -> k
>   a :+ b -> (dimOf a) + (dimOf b)
>   a :* b -> (dimOf a) * (dimOf b)

Eventually, $s \in \mathbb{S}$ will represent the "size" of a tensor and $D(s) \in \mathbb{N}$ will be the vector space dimension of the space it comes from.


Indices
-------

This is well and good; we have a type, ``Size``, that will eventually represent the size of a multidimensional array, and we can extract the "shape" and "dimension" of a size. But we also need a reasonable understanding of how to refer to the entries of an array of a given size.

However we define indices, which indices make sense for a given size will depend on the structure of the size. For instance, a natural number size $k$ might be indexed by $k$ contiguous natural numbers, starting from 0 or 1 or whatever. A product-shaped size like $a \otimes b$ might be indexed by a pair $(u,v)$, where $u$ is an index of $a$ and $v$ an index of $b$. The sum size is a little stranger: to index $a \oplus b$, we need an index for either $a$ or $b$, and some way to distinguish which is which.

Putting this together, we will define an algebra of indices like so.

<div class="result">
<div class="defn">
<p>We denote by $\mathbb{I}$ the free algebra over $\mathbb{N}$ with two function symbols of arity 1 and one of arity 2, denoted $\mathsf{L}$, $\mathsf{R}$, and $\&$. Elements of $\mathbb{I}$ are called <em>indices</em>, and we'll sometimes refer to $\mathbb{I}$ as the <em>algebra of indices</em>.</p>
</div>
</div>

Again, since $\mathbb{I}$ is a free algebra we can represent it as an algebraic type.

> data Index
>   = Index Integer
>   | L Index
>   | R Index
>   | Index :& Index
>   deriving Eq
> 
> 
> instance Show Index where
>   show = \case
>     Index k -> show k
>     L a     -> "L(" ++ show a ++ ")"
>     R b     -> "R(" ++ show b ++ ")"
>     a :& b  -> concat ["(", show a, ",", show b, ")"]
> 
> 
> instance Num Index where
>   fromInteger = Index
> 
>   (+)    = error "Index Num instance: (+) does not make sense"
>   (*)    = error "Index Num instance: (*) does not make sense"
>   negate = error "Index Num instance: negate does not make sense"
>   abs    = error "Index Num instance: abs does not make sense"
>   signum = error "Index Num instance: signum does not make sense"

Now given an index and a size, it may or may not make sense to talk about an entry at the index in a structure of the given size -- like asking for the item at index 10 in an array of length 5. To capture this, we define a <em>compatibility relation</em> to detect when an index can be used on a given size.

> isIndexOf :: Index -> Size -> Bool
> (Index t) `isIndexOf` (Size k)
>   = 0 <= t && t < k
> (L u) `isIndexOf` (a :+ _)
>   = isIndexOf u a
> (R v) `isIndexOf` (_ :+ b)
>   = isIndexOf v b
> (u :& v) `isIndexOf` (a :* b)
>   = (u `isIndexOf` a) && (v `isIndexOf` b)
> _ `isIndexOf` _
>   = False

From now on, if $s$ is a size, I'll also use $s$ to denote the set of indices compatible with $s$. So for example, if $s = 5$, we might say somthing like $$\sum_{i \in s} f(i)$$ without ambiguity.

We'd like to be able to construct $s$ as a list; this is what ``indicesOf`` does. I'm going to play a little fast and loose with the proof because laziness.

> indicesOf :: Size -> [Index]
> indicesOf = \case
>   Size k -> map Index [0..(k-1)]
>   a :+ b -> map L (indicesOf a) ++ map R (indicesOf b)
>   a :* b -> [ u :& v | v <- indicesOf b, u <- indicesOf a ]

The number of different indices for a given size should be equal to the size's dimension. This suggests a simple test: the length of the index list is the dimension, and all entries of the index list are distinct.

> _test_index_count :: Test (Size -> Bool)
> _test_index_count =
>   testName "dimOf s == length $ indicesOf s" $
>   \s ->
>     (dimOf s) == (fromIntegral $ length $ indicesOf s)
> 
> _test_indices_distinct :: Test (Size -> Bool)
> _test_indices_distinct =
>   testName "indicesOf s all distinct" $
>   \s -> (indicesOf s) == (nub $ indicesOf s)

In later posts, $s \in \mathbb{S}$ will represent the size (and shape) of the elements in a vector space consisting of tensors, which itself has vector space dimension $D(s)$. But it will sometimes be convenient to think of these tensors canonically as $D(s)$-dimensional vectors. To do this, we'll set up a bijection between the indices of a given size $s$ and the natural numbers less than $D(s)$. I'll call the function from indices to numbers "flatten", since it turns a complicated thing into a one-dimensional thing, and call the inverse "buildup".

> flatten :: Size -> Index -> Integer
> flatten (Size k) (Index t)
>   = if 0 <= t && t < k then t else error "index out of bounds"
> flatten (a :+ _) (L u)
>   = flatten a u
> flatten (a :+ b) (R v)
>   = (dimOf a) + (flatten b v)
> flatten (a :* b) (u :& v)
>   = (flatten a u) + (flatten b v)*(dimOf a)
> 
> 
> buildup :: Size -> Integer -> Index
> buildup (Size k) t
>   = if 0 <= t && t < k
>       then Index t
>       else error "integer index out of bounds"
> buildup (a :+ b) t
>   = if t < dimOf a
>       then L $ buildup a t
>       else R $ buildup b (t - dimOf a)
> buildup (a :* b) t
>   = (buildup a (t `rem` (dimOf a))) :& (buildup b (t `quot` (dimOf a)))

Now ``flatten`` and ``buildup`` should be inverses of each other, which we can test.

> _test_flatten_buildup :: Test (Size -> Bool)
> _test_flatten_buildup =
>   testName "flatten s . buildup s == id" $
>   \s ->
>     let ks = [0..((dimOf s) - 1)]
>     in ks == map (flatten s . buildup s) ks
> 
> _test_buildup_flatten :: Test (Size -> Bool)
> _test_buildup_flatten =
>   testName "buildup s . flatten s == id" $
>   \s ->
>     let ks = indicesOf s
>     in ks == map (buildup s . flatten s) ks

To wrap up, in this post we defined two algebraic types, ``Size`` and ``Index``, to represent the sizes and indices of multidimensional arrays, and two functions, ``flatten`` and ``buildup``, that canonically map the indices of a given size to a 0-indexed list of natural numbers.

In the next post, we'll use ``Size`` and ``Index`` to define and manipulate multidimensional arrays.


Tests
-----

Math heavy code is well suited to automated tests, so we'll write some along the way using the ``QuickCheck`` library.

First off, we won't be needing the full complexity of QuickCheck, so here are some helper functions to make the tests a little simpler to write.

> type Test prop = (String, prop)
> 
> testName :: String -> prop -> Test prop
> testName name prop = (name, prop)
> 
> runTest, skipTest :: Testable prop => Args -> Test prop -> IO ()
> runTest args (name, prop) = do
>   putStrLn ("\x1b[1;34m" ++ name ++ "\x1b[0;39;49m")
>   result <- quickCheckWithResult args prop
>   if isSuccess result
>     then return ()
>     else (putStrLn (show result)) >> exitFailure
> 
> -- when testing tests
> skipTest _ (name, _) =
>   putStrLn ("\x1b[1;33mskipped: " ++ name ++ "\x1b[0;39;49m")
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\n\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
> 
> class TypeName t where
>   typeName :: t -> String
> 
> instance TypeName Int     where typeName _ = "Int"
> instance TypeName Integer where typeName _ = "Integer"
> instance TypeName Double  where typeName _ = "Double"
> 
> pairOf :: (Monad m) => m a -> m b -> m (a,b)
> pairOf ma mb = do
>   x <- ma
>   y <- mb
>   return (x,y)
> 
> forAll2 :: (Show a, Show b, Testable prop)
>   => Gen a -> Gen b -> (a -> b -> prop) -> Property
> forAll2 ga gb f = forAll genPair (uncurry f)
>   where
>     genPair = do
>       x <- ga
>       y <- gb
>       return (x,y)
> 
> forAll3 :: (Show a, Show b, Show c, Testable prop)
>   => Gen a -> Gen b -> Gen c -> (a -> b -> c -> prop) -> Property
> forAll3 ga gb gc f = forAll genTriple g
>   where
>     genTriple = do
>       x <- ga
>       y <- gb
>       z <- gc
>       return (x,y,z)
> 
>     g (x,y,z) = f x y z

To write QuickCheck tests for a given type it needs to be an instance of ``Arbitrary``, which provides two basic functions: ``arbitrary``, which generates a "random" element of the type, and ``shrink``, which takes an element and makes it "smaller" in some way. Defining these functions for a given type may be ugly, but only has to be done once.

> instance Arbitrary Size where
>   arbitrary = sized arbSize
> 
>   shrink = \case
>     Size k -> if k <= 0 then [] else [Size (k-1)]
>     u :+ v -> [u, v]
>     u :* v -> [u, v]
> 
> arbSize :: Int -> Gen Size
> arbSize 0 = do
>   k <- elements [0,1,1,2,2,2,2]
>   return (Size k)
> arbSize n = do
>   switch <- arbitrary :: Gen Int
>   m <- choose (1,n)
>   case switch `mod` 5 of
>     0 -> do
>       u <- arbSize $ n-1
>       v <- arbSize $ n-1
>       return (u :* v)
>     1 -> do
>       u <- arbSize $ n-1
>       v <- arbSize $ n-1
>       return (u :+ v)
>     _ -> do
>       k <- elements [0,1,2]
>       return (Size k)

Now we can wrap up our tests in a little suite, ``_test_index``. The arguments for this function are (1) the number of test cases to generate and (2) how big they should be.

> -- run all tests for Size and Index
> _test_index :: Int -> Int -> IO ()
> _test_index num size = do
>   testLabel "Size and Index"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args _test_index_count
>   runTest args _test_indices_distinct
>   runTest args _test_flatten_buildup
>   runTest args _test_buildup_flatten
> 
> main_index :: IO ()
> main_index = _test_index 200 20
