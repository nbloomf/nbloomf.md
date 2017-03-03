---
title: Relative references for Löb spreadsheets
author: nbloomf
date: 2017-02-28
tags: haskell
---

This post is literate Haskell; you can copy and paste the contents to a module or just download the [source file](https://github.com/nbloomf/nbloomf.md/posts/2017-02-28-relative-references-for-loeb-spreadsheets.lhs) directly and play with it on your own machine. As usual, we need to start with some pragmas and imports.

```haskell

> {-# LANGUAGE MultiParamTypeClasses #-}
> 
> module Sheet where
> 
> import Data.Monoid

```

Some years ago I read a [blog post](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html) by Dan Piponi which includes the following statement:

<quote>So here's a way to write code: pick a theorem, find the corresponding type, and find a function of that type.</quote>

Dan then takes a result known as [Löb's Theorem](https://en.wikipedia.org/wiki/L%C3%B6b's_theorem) in modal logic and shows how one "implementation" of this theorem acts like a spreadsheet evaluator. (!) At the time I remember thinking this was pretty neat, but the depth of this strategy for finding useful abstractions went over my head.

More recently I was reading that post again and it occurred to me that with some tweaking, Dan's ``loeb`` function could probably form the basis of a practical, functional spreadsheet program. To recap, Löb's theorem is the following modal logic statement: $$\square(\square P \rightarrow P) \rightarrow \square P.$$

One way to interpret that statement as a type is like this:

```haskell
loeb :: (Functor f) => f (f x -> x) -> f x
```

and one possible definition for such a function is this:

```haskell
loeb x = fmap (\a -> a (loeb x)) x
```

For example, ``loeb`` will take a list of functions that each take a list of integers and return an integer and then return a list of integers. This allows us to define lists that refer back to parts of themselves and evaluate them in a meaningful way -- like a spreadsheet.

One thing ``loeb`` *can't* do is handle relative references. For example, we can have a cell that says "add 1 to the number at cell index 2", but not one that says "add 1 to the number at the cell with index 5 less than mine". Of course relative references are an important feature of real spreadsheets, since they vastly simplify common operations like fill and paste.

Kenny Foner addressed this by replacing the ``Functor`` constraint on ``f`` with ``ComonadApply``, and wrapped this in a library called [ComonadSheet](https://github.com/kwf/ComonadSheet). The result is an infinite, lazy, $n$-dimensional spreadsheet. Have a look -- that library and its documentation are full of insights.

Today I'm interested in a different approach to relative references. The fundamental barrier to using relative references with ``loeb`` is that each cell needs to know something about it's "address" within the spreadsheet. For example, in a list, each entry has a position of type ``Int``; in a matrix, each entry has a position of type ``(Int, Int)``, and so on. The important thing about this position is that (1) every entry has one and (2) they are all distinct. Normally I'd refer to a position like this as an *index*, but unfortunately the term "Indexed Functor" already means something. And wouldn't you know it, the concept of a functor with index information already lives in the Lens library, where it goes by the name [FunctorWithIndex](http://hackage.haskell.org/package/lens-4.15.1/docs/Control-Lens-Indexed.html#t:FunctorWithIndex). To avoid pulling in too many dependencies I'll roll my own simplified version of this class, called an *Addressable*.

```haskell

> -- t is the "container type"
> -- n is the "address type"
> class Addressable t n where
>
>   -- extract the entry at a given address
>   -- (not necessarily a total function)
>   at :: t a -> n -> a
> 
>   -- replace each entry by its address
>   addresses :: t a -> t n
> 
>   -- address-aware mapping
>   amap :: (n -> a -> b) -> t a -> t b

```

For example, here's an implementation for lists. Note that I prefer to think of lists as 1 indexed. :)

```haskell

> instance Addressable [] Int where
>   as `at` n = as !! (n-1)
> 
>   addresses = map fst . zip [1..]
> 
>   amap f xs = map (uncurry f) $ zip (addresses xs) xs

```

And finally, the ``loeb`` function with appropriate changes. I've renamed it to ``eval``, because (1) that name is suggestive of what the function does and (2) the type isn't Löb's Theorem anymore! The ``eval'`` version is tweaked from Piponi's ``loeb``, and ``eval`` is cribbed from Foner's fixpoint-based version of ``loeb``.

```haskell

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

```

The type of ``eval`` looks like the statement $$\square(Q \rightarrow (\square P \rightarrow P)) \rightarrow \square P,$$ and I have no idea if that means anything in the context of modal logic (I doubt it!).

Now to use ``eval``, our "spreadsheet" will consist of functions that take both an address and a spreadsheet. This ``Num`` instance for functions will be handy:

```haskell

> instance Show (x -> a)
> instance Eq (x -> a)
> 
> instance (Num a, Eq a) => Num (x -> a) where
>   fromInteger = const . fromInteger
>   f + g = \x -> f x + g x
>   f * g = \x -> f x * g x
>   negate = (negate .)
>   abs = (abs .)
>   signum = (signum .)

```

And a type synonym for convenience:

```haskell

> type Sheet x = [Int -> [x] -> x]

```

Now we can define boring spreadsheet-like lists like so:

```haskell

> test1 :: Sheet Int
> test1 = [ 1, 3, 6 + 5 ]

```

Try evaluating this with ``eval test1``. Woo!

Note that the literal integers ``1``, ``3``, et cetera are not of type ``Int``, but type ``Int -> [Int] -> Int``, and that ``+`` operates not on ``Int``s but on functions.

Useful spreadsheets include cell references, both absolute (get the value in cell 2) and relative (get the value in the cell 3 slots to the right). We'll introduce a type and some helper functions to make this simpler.

```haskell

> -- type representing a reference
> data Ref n = Abs n | Rel n
> 
> ref :: (Addressable t n, Monoid n)
>   => Ref n -> n -> t x -> x
> 
> ref (Abs k) _ xs = xs `at`            k
> ref (Rel k) i xs = xs `at` (mappend i k)
> 
> refAbs k = ref (Abs k)
> refRel k = ref (Rel k)
> 
> 
> instance Monoid Int where
>   mappend = (+)
>   mempty  = 0

```

Now we can write cells that refer to each other, both absolutely and relatively, like so. (Try these out with ``eval`` too.)

```haskell

> test2 :: Sheet Int
> test2 =
>   [ 1
>   , refAbs 1
>   , refRel 1 + refRel (-2)
>   , 5
>   , const length
>   ]
>
> test3 :: Sheet Integer
> test3 = [0,1] ++ repeat (refRel (-1) + refRel (-2))

```
