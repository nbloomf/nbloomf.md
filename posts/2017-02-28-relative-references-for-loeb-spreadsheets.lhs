---
title: Relative references for Löb spreadsheets
author: nbloomf
date: 2017-02-28
tags: haskell
---

This post is literate Haskell; you can copy and paste the contents to a module or just download the [source file](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-02-28-relative-references-for-loeb-spreadsheets.lhs) directly, load it in GHCi, and play with it on your own machine. As usual, we need to start with some pragmas and imports.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleInstances #-}
> 
> module LoebSheets where
> 
> import Data.Monoid
> import Control.Applicative

Some years ago I read a [blog post](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html) by Dan Piponi which includes the following statement:

<blockquote>So here's a way to write code: pick a theorem, find the corresponding type, and find a function of that type.</blockquote>

Dan then takes a result known as [Löb's Theorem](https://en.wikipedia.org/wiki/L%C3%B6b's_theorem) in modal logic and shows how one "implementation" of this theorem acts like a spreadsheet evaluator. (!) At the time I remember thinking this was pretty neat, but the depth of this strategy for finding useful abstractions went over my head.

More recently I was reading that post again and it occurred to me that with some tweaking, Dan's ``loeb`` function could probably form the basis of a practical functional spreadsheet program. To recap, Löb's theorem is the following modal logic statement: $$\square(\square P \rightarrow P) \rightarrow \square P.$$

One way to interpret that statement as a type is like this:

```haskell
loeb :: (Functor f) => f (f x -> x) -> f x
```

and one possible definition for such a function is this:

```haskell
loeb x = fmap (\a -> a (loeb x)) x
```

For example, ``loeb`` will take a list of functions that each take a list of integers and return an integer and then return a list of integers. This allows us to define lists that refer back to parts of themselves and evaluate them in a meaningful way -- like a spreadsheet.

One thing ``loeb`` *can't* do is handle relative references. For example, we can have a cell that says "add 1 to the number at cell index 2", but not one that says "add 1 to the number at the cell with index 5 less than mine". Of course relative references are an important feature of real spreadsheets, so this is a problem.

Kenny Foner addressed this by replacing the ``Functor`` constraint on ``f`` with ``ComonadApply``, and wrapped this in a library called [ComonadSheet](https://github.com/kwf/ComonadSheet). The result is an infinite, lazy, $n$-dimensional spreadsheet. Have a look -- that library and its documentation have some interesting things to say.

Today I'm interested in a different approach to relative references. The fundamental barrier to using relative references with ``loeb`` is that each cell needs to know something about it's "address" within the spreadsheet. For example, in a list, each entry has a position of type ``Int``; in a matrix, each entry has a position of type ``(Int, Int)``, and so on. The important thing about this position is that (1) every entry has one and (2) they are all distinct. Normally I'd refer to a position like this as an *index*, but unfortunately the term "Indexed Functor" already means something. And wouldn't you know it, the concept of a functor with index information already lives in the Lens library, where it goes by the name [FunctorWithIndex](http://hackage.haskell.org/package/lens-4.15.1/docs/Control-Lens-Indexed.html#t:FunctorWithIndex). To avoid pulling in too many dependencies I'll roll my own simplified version of this class, called an *Addressable*. For convenience, I'll make it depend on ``Applicative``.

> -- t is the "container type"
> -- n is the "address type"
> class (Applicative t) => Addressable t n | t -> n where
>
>   -- extract the entry at a given address
>   -- (not necessarily a total function)
>   at :: t a -> n -> a
> 
>   -- replace each entry by its address
>   addresses :: t a -> t n

And we need an address-aware version of ``fmap``.

> -- address-aware mapping
> amap :: (Applicative t, Addressable t n)
>   => (n -> a -> b) -> t a -> t b
> amap f xs = f <$> (addresses xs) <*> xs

For example, here's an implementation for [``ZipLists``](https://hackage.haskell.org/package/base-4.9.1.0/docs/Control-Applicative.html#t:ZipList). (We need to use ``ZipList``s to get the right ``Applicative`` implementation.) Note that I prefer to think of lists as 1 indexed. :)

> instance Addressable ZipList Int where
>   (ZipList as) `at` n = as !! (n-1)
> 
>   addresses as = const <$> (ZipList [1..]) <*> as

And finally, the ``loeb`` function with appropriate changes. I've renamed it to ``eval``, because (1) that name is suggestive of what the function does and (2) the type isn't Löb's Theorem anymore! The ``eval'`` version is tweaked from Piponi's ``loeb``, and ``eval`` is cribbed from Foner's fixpoint-based version of ``loeb``.

> -- slow
> eval' :: (Addressable t n) => t (n -> t x -> x) -> t x
> eval' x = amap (\i a -> a i (eval' x)) x
> 
> -- fast
> eval :: (Addressable t n) => t (n -> t x -> x) -> t x
> eval x = fix $ \y -> amap (\i a -> a i y) x
> 
> fix :: (a -> a) -> a
> fix f = let x = f x in x

The type of ``eval`` looks like the statement $$\square(Q \rightarrow (\square P \rightarrow P)) \rightarrow \square P,$$ and I have no idea if that means anything in the context of modal logic (I doubt it!).

Now to use ``eval``, our "spreadsheet" will consist of functions that take both an address and a spreadsheet. This ``Num`` instance for functions will be handy:

> instance Show (x -> a) where show = undefined
> instance Eq (x -> a) where (==) = undefined
> 
> instance (Num a, Eq a) => Num (x -> a) where
>   fromInteger = const . fromInteger
>   f + g = \x -> f x + g x
>   f * g = \x -> f x * g x
>   negate = (negate .)
>   abs = (abs .)
>   signum = (signum .)

And a type synonym for convenience:

> -- t is the "container" type
> -- n is the "address" type
> -- x is the "value" type
> type Sheet t n x = t (n -> t x -> x)

Now we can define boring spreadsheet-like lists like so:

> test1 :: Sheet ZipList Int Int
> test1 = ZipList [ 1, 3, 6 + 5 ]

Try evaluating this with ``eval test1``. Woo!

Note that the literal integers ``1``, ``3``, et cetera are not of type ``Int``, but type ``Int -> [Int] -> Int``, and that ``+`` operates not on ``Int``s but on functions.

Useful spreadsheets include cell references, both absolute (get the value in cell 2) and relative (get the value in the cell 3 slots to the right). We'll introduce some helper functions to make this simpler.

> refAbs, refRel :: (Addressable t n, Monoid n)
>   => n -> n -> t x -> x
> 
> refAbs k _ xs = xs `at`            k
> refRel k i xs = xs `at` (mappend i k)

Making the "address" type an instance of monoid makes this code more polymorphic. An instance for ``Int`` will be handy:

> instance Monoid Int where
>   mappend = (+)
>   mempty  = 0

Now we can write cells that refer to each other, both absolutely and relatively, like so. (Try these out with ``eval`` too.)

> test2 :: Sheet ZipList Int Int
> test2 = ZipList
>   [ 1
>   , refAbs 1
>   , refRel 1 + refRel (-2)
>   , 5
>   , const (length . getZipList)
>   ]

Here's another: this "spreadsheet" constructs the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_number).

> test3 :: Sheet ZipList Int Integer
> test3 = ZipList $ [0,1] ++
>   repeat (refRel (-1) + refRel (-2))


Again, with Trees
-----------------

Of course the whole point of polymorphism is that the same code can apply to different data. So let's try again, this time with a binary tree shaped spreadsheet. First we roll a quick type:

> data Tree x
>   = E                     -- empty
>   | B x (Tree x) (Tree x) -- branch
>   deriving (Eq, Show)
> 
> instance Functor Tree where
>   fmap _  E        = E
>   fmap f (B x l r) = B (f x) (fmap f l) (fmap f r)
>
> instance Applicative Tree where
>   pure x = B x E E
> 
>   (B f l1 r1) <*> (B x l2 r2) =
>     B (f x) (l1 <*> l2) (r1 <*> r2)

And a couple of utilities for working with trees:

> -- "take" for trees
> prune :: Int -> Tree x -> Tree x
> prune k t
>   | k <= 0    = E
>   | otherwise = case t of
>       E       -> E
>       B x a b -> B x (prune (k-1) a) (prune (k-1) b)
> 
> -- list elements using inorder traversal
> inord :: Tree x -> [x]
> inord  E        = []
> inord (B x a b) = (inord a) ++ [x] ++ (inord b)

Now how can we "address" the nodes in a binary tree? With lists a single integer sufficed, and making the integer signed allowed both absolute and relative references. There's probably a clever way to encode the position of a tree node as an integer, but I'm feeling lazy -- I'll just say that from any node we can travel to the left branch, to the right branch, or up to the parent.

> -- L -> go left, R -> go right, U -> go up
> data Dir = L | R | U deriving (Eq, Show)
>
> 
> instance Addressable Tree [Dir] where
>   at t ps = let qs = norm ps in at' t qs
>     where
>       at' (B x _ _) []     = x
>       at' (B _ l _) (L:es) = at' l es
>       at' (B _ _ r) (R:es) = at' r es
>       at' _ _ = undefined
> 
>       -- normalize a list of Dirs
>       norm :: [Dir] -> [Dir]
>       norm []      = []
>       norm (U:x)   = norm x
>       norm (L:U:x) = norm x
>       norm (R:U:x) = norm x
>       norm (d:x)   = d : norm x
> 
>   addresses x = f x []
>     where
>       f E _ = E
> 
>       f (B _ l r) ds
>         = B (reverse ds) (f l (L:ds)) (f r (R:ds))

Now ``[Dir]`` is a monoid for free, and we can do things like this:

> test4 :: Sheet Tree [Dir] Int
> test4 =
>   B 10
>    (B 2
>      (B (1 + refAbs []) E E)
>      (B (refRel [U,L] + refRel [U,U]) E E))
>    (B 7
>      (B 4 E E)
>      (B 5 E E))

Working with tree shaped "spreadsheets" is a little less natural than lists or matrices, but I suspect that is because they are less familiar. Here's another example:

> mediant :: (Num a) => ((a,a),(a,a)) -> (a,a)
> mediant ((x1,y1),(x2,y2)) = (x1+x2, y1+y2)
> 
> test5 :: Sheet Tree [Dir] ((Int, Int), (Int, Int))
> test5 = B (\_ _ -> ((0,1),(1,0))) tL tR
>   where
>     tL = B (fL $ refRel[U]) tL tR
>     tR = B (fR $ refRel[U]) tL tR
> 
>     fL = \f h k -> let (x,y) = f h k in (x, mediant (x,y))
>     fR = \f h k -> let (x,y) = f h k in (mediant (x,y), y)

This one is awkward -- there are likely to be several helper functions we could factor out here. But what does it do? Try this:

```haskell
$> prune 5 $ eval test5
$> fmap mediant $ prune 5 $ eval test5
$> inord $ fmap mediant $ prune 5 $ eval test5
```

This "spreadsheet" constructs the [Stern-Brocot tree](https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree) of positive rational numbers. Woo!


One Step Further
----------------

If we have an applicative functor and it makes sense to assign the contents "addresses", we have a kind of spreadsheet, and can use both absolute and relative references. Just out of curiosity, we can also have references that depend on a computed value like so.

> crefAbs, crefRel :: (Addressable t n, Monoid n)
>   => (n -> t n -> n) -> n -> t n -> n
> 
> crefAbs f i xs = xs `at`            (f i xs)
> crefRel f i xs = xs `at` (mappend i (f i xs))

Note that ``crefAbs`` and ``crefRel`` look a lot like ``refAbs`` and ``refRel``, except that they apply a context function. These act like the ``Indirect`` or ``Index`` functions in Excel -- they let us compute a cell reference (absolute or relative) on the fly.

> test6 :: Sheet ZipList Int Int
> test6 = ZipList
>   [ 1
>   , 1 + crefAbs (2 + refRel (-1))
>   , 5
>   ]

I don't quite have the motivation to turn this into an actual GUI-driven spreadsheet, so I'll leave that part as an exercise. :)

But I am curious -- are there any other interesting applicative functors with addresses? Can oddly "shaped" spreadsheets do interesting things that array shaped ones can't?

I'll end with a trivial ``main`` so this module can be typechecked as a test.

> main :: IO ()
> main = putStrLn "ok"
