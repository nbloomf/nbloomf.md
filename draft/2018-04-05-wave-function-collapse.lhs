---
title: Wave Function Collapse
author: nbloomf
date: 2018-04-05
tags: literate-haskell
---

I'm a little late to the party, but I recently came across Maxim Gumin's [Wave Function Collapse](https://github.com/mxgmn/WaveFunctionCollapse) algorithm for procedurally generating graphics. If you haven't seen it before, go check out that link -- it's really neat. In a nutshell, WFC makes it possible to generate large images in the "style" of a much smaller input image. The main idea is to put a probability distribution on each pixel in the output image, weighted on a distribution determined by the input image, and "collapse" the output image by "observing" one pixel at a time and updating the distribution. It's a simple idea that yields really nifty results.

Anyway, I came across the WFC algorithm and wanted to play with it myself, which is what we'll try to do in this post. Usually WFC is used to procedurally generate maps and such for games, but I just want to try making pretty pixelated pictures. I'm going to try to implement the algorithm as closely as I can. I don't know anything about C#, so we'll see how well it goes! :)

As usual on this blog I'll be writing in Haskell, so we start with some compiler noises.

> {-# LANGUAGE RecordWildCards, GADTs, ScopedTypeVariables, BangPatterns #-}
> module WaveFunctionCollapse where

`RecordWildCards` is just some syntactic sugar to make records nicer to work with. We'll also use the following imports.

> import Prelude hiding (init, break, read)
> import Data.IORef
> import Data.List (unlines)
> import Control.Monad
> import Control.Monad.IO.Class
> import System.Exit
> import qualified System.Random as R
> import qualified Data.Array.IO as A
> import qualified Codec.Picture as JP
> import qualified Data.ByteString as B
> import qualified Data.HashMap.Strict as HM



Mimicking C#
------------

As an exercise I'll try to translate the original C# code as directly as possible, because Maxim and collaborators have already put some effort into making it efficient, and I am lazy. The code is not very long -- a few hundred lines -- and doesn't use any fancy language features.

There are two basic problems we'll need to address before porting the code: how to deal with mutable data, and how to mimic imperativeness (imperativity?).

Haskell *really* doesn't like mutable data, and WFC is basically all mutable data. But I think we can get by on this front with `IORef`s and mutable arrays.

Translating the imperativeness of C# is a different beast. Haskell's *do* notation gets us pretty close, but there are a couple of fundamental ideas in C-derived semantics that require some care. First is C#'s `return` statement, which is totally unrelated to Haskell's `return` -- it means "forget whatever you were about to do next and give this value to the context above you". Second is the semantics of for loops, and specifically the way `break` and `continue` work. Haskell's standard looping constructs (like `map` and friends) don't immediately lend themselves to behaving like `for` in the presence of `break` and `continue`.

I'll solve these problems with (drumroll please...) types.



`return`
========

First off, let's think about `return`. Right off the bat, let's rename C#'s `return` as `exitEarly`, since that's what it does, and to avoid confusion with Haskell's `return`.

In many imperative languages, every statement has an implicit *value*. If that value isn't used, it's just thrown away. Let's make this idea explicit. At any given point in an imperative program's execution, there are two different futures waiting for the value of the current line: there's the next command in the program, and the command that created the context the line is executing in. We can create a wrapper type, `Future`, to indicate which of these possible futures a value should be passed to.

> data Future t u
>   = ExitEarly t
>   | KeepGoing u
>   deriving (Eq, Show)

`ExitEarly` means *pass this to the calling context*, and `KeepGoing` means *pass this to the next command*. Now `Future t` is itself a monad in the `KeepGoing` type. Let's think about how.

`fmap` applies a function to a value in context. The value stored in `ExitEarly` is somehow *outside* of the context, since it triggers a halt of whatever computation is being done.

> instance Functor (Future t) where
>   fmap _ (ExitEarly t) = ExitEarly t
>   fmap f (KeepGoing u) = KeepGoing (f u)

`pure` puts a single value into context. `<*>` applies a function in context to a value in context, where the context is short-circuited by `ExitEarly`.

> instance Applicative (Future t) where
>   pure u = KeepGoing u
> 
>   (ExitEarly t) <*> _ = ExitEarly t
>   _ <*> (ExitEarly t) = ExitEarly t
>   (KeepGoing f) <*> (KeepGoing x) = KeepGoing (f x)

And `>>=` is also short circuited by `ExitEarly`.

> instance Monad (Future t) where
>   return = pure
> 
>   (ExitEarly t) >>= _ = ExitEarly t
>   (KeepGoing u) >>= f = f u

Lo and behold, we've reinvented the `Either` monad with a different name. I think the new name is better here, though, since it reminds us of how we're interpreting the different possible `Future`s.

That's nice and all, but to implement WFC we're going to need to do lots of IO. We can seamlessly integrate `IO` and `Future` with a hand-rolled monad stack, which we'll call `Imp`. Imp is short for *imperative*, but it's not quite imperative -- only a little imp-ish. HO HO

> newtype Imp r a = Imp
>   { unImp :: IO (Future r a) }

And the instances, which are more or less forced:

> instance Functor (Imp r) where
>   fmap f x = Imp $ do
>     z <- unImp x
>     case z of
>       ExitEarly r -> return $ ExitEarly r
>       KeepGoing a -> return $ KeepGoing (f a)
> 
> instance Applicative (Imp r) where
>   pure a = Imp $ do
>     return $ KeepGoing a
> 
>   f <*> x = Imp $ do
>     u <- unImp f
>     case u of
>       ExitEarly r -> return $ ExitEarly r
>       KeepGoing g -> do
>         v <- unImp x
>         case v of
>           ExitEarly s -> return $ ExitEarly s
>           KeepGoing y -> return $ KeepGoing (g y)
> 
> instance Monad (Imp r) where
>   return = pure
> 
>   x >>= f = Imp $ do
>     z <- unImp x
>     case z of
>       ExitEarly r -> return $ ExitEarly r
>       KeepGoing a -> unImp $ f a

It will be handy to be able to lift arbitrary `IO` actions to the `Imp` monad.

> instance MonadIO (Imp r) where
>   liftIO x = Imp $ do
>     a <- x
>     return $ KeepGoing a

Note that we've implemented `Imp` so that the `ExitEarly` value and the `KeepGoing` value can have different types. But in the end, a single C# function should only be able to return a value of a single type, whether it was returned early or not. The next function will enforce this.

> runImp :: Imp a a -> IO a
> runImp x = do
>   z <- unImp x
>   case z of
>     ExitEarly a -> return a
>     KeepGoing a -> return a

Finally, we define a bit of syntax for early exits.

> exitEarly :: r -> Imp r a
> exitEarly r = Imp $ do
>   return $ ExitEarly r

Let's look at an example to see how `Imp` can look a little bit imperative: try to reason about what `test1 True` and `test1 False` do.

> test1 :: Bool -> IO Int
> test1 p = runImp $ do
>   if p
>     then exitEarly 1
>     else return ()
>   return 2



`break` and `continue`
======================

Ok: the `Imp` monad lets us model computations that can return to their calling context early; it's basically a stack of `IO` and `Either`. Now let's tackle `for` loops with `break` and `continue`.

How do for loops work? Let's start with the syntax.

```
for (initialize; end condition; mutate) {
  body
}
```

`for` first runs `initialize`, then runs `body` repeatedly. After each loop it runs `mutate`, and before each run it evaluates `end condition` to determine whether to keep going.

In Haskell, the idiomatic way to iterate over some values is with a list. We'll keep this idea.

But note that there are basically 3 ways we can exit a given iteration of `body`: either we reach a `break` statement, or we reach a `continue` statement, or we get to the end of `body`'s list of statements. Let's represent this with a type!

> data Loop u
>   = Loop
>   | Break u
>   | Continue
>   deriving (Eq, Show)

(Forget about that `u` type parameter for now.)

So `Loop` represents the possible ways to exit a `for` body. Going a step further, we can think of the `for` body itself as a *mapping* from an index value to one of these possible exit conditions. In an imperative language, the only other thing the body can do is have side effects.

A reasonable first attempt at a type signature for `for` loops is something like this:

```
forloop
  :: (Monad m)          -- context for side effects
  => [a]                -- list to iterate over
  -> (a -> m (Loop u))  -- loop body
  -> m ()
```

And this would certainly work -- but it has a subtle weakness. We're going to make a slight tweak, and define for loops like this:

> forLoopM
>   :: (Monad m)
>   => [a]
>   -> u
>   -> (a -> m (Loop u))
>   -> m u
> 
> forLoopM !xs !end f = g xs
>   where
>     g [] = return end
>     g (a:as) = do
>       z <- f a
>       case z of
>         Loop -> g as
>         Break u -> return u
>         Continue -> g as

And a few helper functions to cut down on `return`s:

> loop :: (Monad m) => m (Loop u)
> loop = return Loop
> 
> break :: (Monad m) => u -> m (Loop u)
> break u = return $ Break u
> 
> continue :: (Monad m) => m (Loop u)
> continue = return Continue

That extra `u` parameter gives us a way to signal to the caller how this loop ended; either it made it to the end, or we broke out of the loop at some stage. By the way, we can see now that the `Continue` case is redundant -- it is exactly the same as `Loop`. We'll keep it around just for fun.

Let's see an example.

> test2 :: IO ()
> test2 =
>   forLoopM [1..10] () $ \i -> do
>     case i of
>       3 -> do
>         putStrLn "three"
>         continue
>       7 -> do
>         putStrLn "this is boring."
>         break ()
>       _ -> do
>         putStrLn $ show i
>         loop

That `u` parameter also makes it possible to nest loops.

> test3 :: IO ()
> test3 =
>   forLoopM [1..3] () $ \i -> do
>     putStrLn $ "outer loop " ++ show i
>     forLoopM [1..5] Loop $ \j -> do
>       putStrLn $ "  inner loop " ++ show j
>       if i+j == 6
>         then do
>           putStrLn "    WOO!!"
>           loop
>         else loop

While we're at it, since `forLoopM` can use any monadic context, we can mix it with `exitEarly`.

> test4 :: Int -> IO ()
> test4 k = runImp $ do
>   forLoopM [1..5] () $ \i -> do
>     liftIO $ putStrLn $ show i
>     if i == k
>       then exitEarly ()
>       else loop
>   liftIO $ putStrLn "WOO"

Similarly, we can define while loops. Watch out -- these are not guaranteed to terminate!

> whileLoopM
>   :: (Monad m)
>   => m Bool
>   -> u
>   -> m (Loop u)
>   -> m u
> whileLoopM !test !end body = g
>   where
>     g = do
>       !p <- test
>       if p == False
>         then return end
>         else do
>           z <- body
>           case z of
>             Loop -> g
>             Break u -> return u
>             Continue -> g

Testing... note that the syntax for the stopping condition is painful. We'll address this later.

> test5 :: Int -> IO ()
> test5 m = do
>   x <- newIORef (0 :: Int)
> 
>   -- oof!
>   let
>     carryon :: IO Bool
>     carryon = do
>       u <- readIORef x
>       return $ u < m
> 
>   whileLoopM carryon () $ do
>     u <- readIORef x
>     putStrLn $ show u
>     modifyIORef' x (1+)
>     loop
> 
>   return ()



State
-----

Another feature of C# we need to mimic is state. Since WFC uses only one base class, the member data of that class is effectively global. We could model this with a state monad, but most of our state will be mutable. We can get away with using a reader monad, where the "environment" we store is a bunch of mutable `IORef`s and `IOArray`s (i.e. pointers). It will be handy to implement this in a separate monad, rather than adding it to the `Imp` stack. (We'll see why in a bit.)

There's the usual reader monad stack:

> data Global g a = Global
>   { unGlobal :: g -> IO a }
> 
> runGlobal :: g -> Global g a -> IO a
> runGlobal !gs x = unGlobal x gs

And the usual instances.

> instance Functor (Global g) where
>   fmap f x = Global $ \gs -> do
>     a <- unGlobal x gs
>     return $ f a
> 
> instance Applicative (Global g) where
>   pure a = Global $ \_ -> return a
> 
>   f <*> x = Global $ \gs -> do
>     g <- unGlobal f gs
>     y <- unGlobal x gs
>     return $ g y
> 
> instance Monad (Global g) where
>   return = pure
> 
>   x >>= f = Global $ \gs -> do
>     a <- unGlobal x gs
>     unGlobal (f a) gs
> 
> instance MonadIO (Global g) where
>   liftIO x = Global $ \_ -> x

`globals` is our name for the function that exposes the global environment "to the current scope", so to speak.

> globals :: Global g g
> globals = Global $ \gs -> return gs

The `Global` monad is parameterized on the global environment type so that we can play with a toy example. Here's a state record consisting of just a counter.

> data ToyState = ToyState
>   { counter :: IORef Int
>   }
> 
> toyState :: Int -> IO ToyState
> toyState k = do
>   counter <- newIORef k
>   return ToyState{..}

Now a function that increments the counter if its value is less than 3.

> increment :: Global ToyState ()
> increment = do
>   -- bring global variables into scope
>   ToyState{..} <- globals
>   liftIO $ runImp $ do
>     i <- liftIO $ readIORef counter
>     liftIO $ putStrLn $ show i
>     if i >= 3
>       then do
>         liftIO $ putStrLn "bailing out!"
>         exitEarly ()
>       else return ()
>     liftIO $ writeIORef counter (i+1)

Finally, a function that runs `increment` five times in a loop.

> test6 :: IO ()
> test6 = do
>   gs@ToyState{..} <- toyState 0
>   runGlobal gs $ do
>     forLoopM [1..5] () $ \j -> do
>       liftIO $ putStrLn $ "value of j is " ++ show j
>       increment
>       loop
>     k <- liftIO $ readIORef counter
>     liftIO $ putStrLn $ "The value of counter is " ++ show k

We need to keep `Global` and `Imp` separate to maintain the semantics of `exitEarly`, which will short-circuit whatever monadic context it is evaluated in. By piling `Global` and `Imp` on each other like this, we can mimic having functions call each other inside a global context, but short circuiting one function does not terminate the entire program, because the type system prevents `exitEarly` from escaping `runImp`.

Here's a helper to make "function calls" explicit.

> call :: (MonadIO m) => g -> Global g a -> m a
> call !gs m = liftIO $ unGlobal m gs

Here's an example with two functions, `ping` and `pong`, that call each other until some global counter reaches 0.

> ping :: Global ToyState ()
> ping = do
>   g@ToyState{..} <- globals
>   liftIO $ runImp $ do
>     liftIO$ modifyIORef' counter ((-1)+)
>     liftIO $ putStrLn "ping!"
>     n <- liftIO $ readIORef counter
>     if n <= 0
>       then liftIO $ putStrLn "whiff!"
>       else call g pong
> 
> pong :: Global ToyState ()
> pong = do
>   g@ToyState{..} <- globals
>   liftIO $ runImp $ do
>     liftIO $ modifyIORef' counter ((-1)+)
>     liftIO $ putStrLn "pong!"
>     n <- liftIO$ readIORef counter
>     if n <= 0
>       then liftIO $ putStrLn "net!"
>       else call g ping
> 
> test7 :: Int -> IO ()
> test7 k = do
>   gs <- toyState k
>   call gs ping



Arrays
------

We'll use mutable `IOArray`s to model arrays. The standard constructor for these is more general than we need, so we'll alias it.

> array1D
>   :: (MonadIO m)
>   => Int
>   -> a
>   -> m (A.IOArray Int a)
> array1D !size init =
>   liftIO $ A.newArray (0, size - 1) init
> 
> array2D
>   :: (MonadIO m)
>   => (Int, Int)
>   -> a
>   -> m (A.IOArray (Int, Int) a)
> array2D (!size1, !size2) init =
>   liftIO $ A.newArray ((0,0), (size1 - 1, size2 - 1)) init
> 
> array3D
>   :: (MonadIO m)
>   => (Int, Int, Int)
>   -> a
>   -> m (A.IOArray (Int, Int, Int) a)
> array3D (!size1, !size2, !size3) init =
>   liftIO $ A.newArray ((0,0,0), (size1 - 1, size2 - 1, size3 - 1)) init

Array length:

> len :: (MonadIO m) => IORef (A.IOArray Int a) -> m Int
> len ref = liftIO $ do
>   arr <- readIORef ref
>   (lo,hi) <- A.getBounds arr
>   return $ hi-lo

It will also be handy to have some functions for pretty printing arrays. First we convert to a list for convenience:

> toList1D :: A.IOArray Int a -> IO [a]
> toList1D arr = do
>   (a1,b1) <- A.getBounds arr
>   forM [a1..b1] $ \i -> do
>     A.readArray arr i
> 
> toList2D :: A.IOArray (Int, Int) a -> IO [[a]]
> toList2D arr = do
>   ((a1,a2),(b1,b2)) <- A.getBounds arr
>   forM [a1..b1] $ \i -> do
>     forM [a2..b2] $ \j -> do
>       A.readArray arr (i,j)

Then pretty print the list with columns aligned.

> print1D :: (Show a) => [a] -> IO ()
> print1D xs = do
>   let m = maximum $ map (length . show) xs
>   putStrLn $ concatMap (leftpad (1+m) . show) xs
> 
> print2D :: (Show a) => [[a]] -> IO ()
> print2D xss = do
>   let m = maximum $ map (length . show) $ concat xss
>   putStrLn $ unlines $ map (concatMap (leftpad (1+m) . show)) xss
> 
> leftpad :: Int -> String -> String
> leftpad k str =
>   reverse $ take k $ (reverse str) ++ (repeat ' ')

For example:

> test8 :: Int -> IO ()
> test8 m = do
>   arr <- array2D (m,m) (0 :: Int)
>   forLoopM [0..(m-1)] () $ \i -> do
>     forLoopM [0..(m-1)] Loop $ \j -> do
>       A.writeArray arr (i,j) ((i*j) `mod` m)
>       loop
>   toList2D arr >>= print2D



Memory
------

WFC makes extensive use of mutable state. We can handle mutable state in Haskell too, using `IORef`s for mutable values and `IOArray`s for mutable arrays, but handling lots of mutable state using the raw APIs for these types can be a little painful. We've seen a few examples so far; we have to read the value of an `IORef` explicitly using `readIORef` and write it with `writeIORef`, and similarly for `IOArrays`. It gets even more cumbersome if we're not in `IO`, since we have to use `liftIO` everywhere. Contrast this with C#, where the syntax for mutation is one character: `=`.

You can learn a lot about a language from what concepts are given the most concise syntax. At one extreme, ML-derived languages denote function application with no syntax at all. Smalltalk does the same to denote message passing, and Lisp for constructing lists. Commands on a Unix shell implicitly read from stdin and write to stdout. In PHP, successfully exiting a function and returning `null` does not require any syntax. This says something deep about what these languages value and how they see the world.

On the other hand concepts that use lots of syntax put a higher burden on the reader, and so it is with mutability in Haskell. We can do it, but the language is really not happy about it. Fortunately, we can do something about this!

Let's model mutable memory locations with a type. We care about two different kinds of mutable memory locations: single values, and cells in an array. We can quibble about whether these two kinds of memory are really so different, but the type system insists that they be kept separate.

> data Memory a where
>   Var :: IORef a -> Memory a
>   (:@) :: (A.Ix i) => IORef (A.IOArray i a) -> i -> Memory a

Note that `Memory` is a GADT, effectively allowing the `i` parameter for array indices be existentially quantified. By the way -- I don't usually like to use the fancier GHC extensions, and this is the very first time I've naturally come across a use for GADTs.

Anyway, what can we do with a mutable memory location? First off, we can inspect the value it holds:

> peek :: (MonadIO m) => Memory a -> m a
> peek x = liftIO $ case x of
>   Var ref -> readIORef ref
>   ref :@ i -> do
>     arr <- readIORef ref
>     A.readArray arr i

And second, we can update the value it holds.

> (=:) :: (MonadIO m) => Memory a -> a -> m ()
> x =: (!a) = liftIO $ case x of
>   Var ref -> writeIORef ref a
>   ref :@ i -> do
>     arr <- readIORef ref
>     A.writeArray arr i a

That `=:` looks a lot like assignment in an imperative language. And sure enough, we can do things like this:

> test9 :: IO ()
> test9 = do
>   -- construct a mutable memory location
>   x <- newIORef (0::Int) >>= (return . Var)
> 
>   forLoopM [1..10] () $ \i -> do
>     peek x >>= print
>     x =: i
>     loop

and this:

> test10 :: IO ()
> test10 = do
>   -- construct a mutable array
>   arr <- array1D 10 (0 :: Int)
>   ref <- newIORef arr
> 
>   forLoopM [0..9] () $ \i -> do
>     (ref :@ i) =: i
>     toList1D arr >>= print1D
>     loop

We can take this a step further, and model mutating assignment operators like `+=`.

> (+=:) :: (MonadIO m, Num a) => Memory a -> a -> m ()
> x +=: (!a) = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> u+a)
>   ref :@ (!i) -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (u+a)
> 
> (*=:) :: (MonadIO m, Num a) => Memory a -> a -> m ()
> x *=: a = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> u*a)
>   ref :@ i -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (u*a)
> 
> (-=:) :: (MonadIO m, Num a) => Memory a -> a -> m ()
> x -=: (!a) = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> u-a)
>   ref :@ (!i) -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (u-a)
> 
> (/=:) :: (MonadIO m, Num a, Fractional a) => Memory a -> a -> m ()
> x /=: a = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> u/a)
>   ref :@ i -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (u/a)
> 
> (//=:) :: (MonadIO m, Num a, Integral a) => Memory a -> a -> m ()
> x //=: a = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> div u a)
>   ref :@ i -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (div u a)
> 
> (.=:) :: (MonadIO m) => Memory [a] -> a -> m ()
> x .=: a = liftIO $ case x of
>   Var ref -> modifyIORef' ref (\u -> a:u)
>   ref :@ i -> do
>     arr <- readIORef ref
>     u <- A.readArray arr i
>     A.writeArray arr i (a:u)

For example:

> test11 :: IO ()
> test11 = do
>   x <- newIORef (0::Int) >>= (return . Var)
> 
>   forLoopM [1..10] () $ \i -> do
>     peek x >>= print
>     x +=: i
>     loop

I should emphasize that this is terrible Haskell code. :)

For example:

> test12 :: IO ()
> test12 = do
>   arr <- A.newArray (1, 10) (1::Int)
>   ref <- newIORef arr
> 
>   forLoopM [1..10] () $ \i -> do
>     (ref :@ i) +=: i
>     loop
> 
>   forLoopM [1..10] () $ \i -> do
>     peek (ref :@ i) >>= print
>     loop

Some convenience functions:

> var :: (MonadIO m) => a -> m (Memory a)
> var a = do
>   ref <- liftIO $ newIORef a
>   return $ Var ref
> 
> (=::) :: (MonadIO m) => IORef a -> m a -> m ()
> ref =:: m = m >>= (liftIO . writeIORef ref)

By the way -- we can similarly define monadic comparisons to make while loops a little nicer.

> (>:) :: (MonadIO m, Ord a) => Memory a -> a -> m Bool
> x >: a = do
>   u <- peek x
>   return $ u > a
> 
> (>=:) :: (MonadIO m, Ord a) => Memory a -> a -> m Bool
> x >=: a = do
>   u <- peek x
>   return $ u >= a
> 
> (<:) :: (MonadIO m, Ord a) => Memory a -> a -> m Bool
> x <: a = do
>   u <- peek x
>   return $ u < a
> 
> notEmptyM :: (MonadIO m) => Memory [a] -> m Bool
> notEmptyM x = do
>   as <- peek x
>   case as of
>     [] -> return False
>     _:_ -> return True
> 
> arrayIsNull :: (MonadIO m, A.Ix i) => IORef (A.IOArray i a) -> m Bool
> arrayIsNull ref = liftIO $ do
>   arr <- readIORef ref
>   bds <- A.getBounds arr
>   return $ null $ A.range bds

For example:

> test13 :: Int -> IO ()
> test13 m = do
>   putStrLn "Have some pseudorandom numbers!"
> 
>   x <- var (0 :: Int)
> 
>   whileLoopM (x <: m) () $ do
>     x +=: 1
>     R.randomRIO (1,100 :: Int) >>= (putStrLn . show)
>     loop
> 
>   return ()

Looping over the entries of an array is a common pattern -- we'll give it it's own function. This can express intent more clearly than just a for loop would.

> arrayLoopM_
>   :: (A.Ix i, MonadIO m)
>   => IORef (A.IOArray i a)
>   -> (i -> m ())
>   -> m ()
> 
> arrayLoopM_ ref f = do
>   arr <- liftIO $ readIORef ref
>   bds <- liftIO $ A.getBounds arr
>   mapM_ f $ A.range bds

We also define some special cases, `arrayFill` writes a value at each index of an array, and `arraySum` adds up the entries.

> arrayFill
>   :: (A.Ix i, MonadIO m)
>   => IORef (A.IOArray i a)
>   -> a
>   -> m ()
> arrayFill ref a = do
>   arrayLoopM_ ref $ \i -> do
>     (ref :@ i) =: a
> 
> arraySum
>   :: (A.Ix i, MonadIO m, Num a)
>   => IORef (A.IOArray i a)
>   -> m a
> arraySum ref = do
>   total <- var 0
>   arrayLoopM_ ref $ \i -> do
>     u <- peek (ref :@ i)
>     total +=: u
>   peek total >>= return

A helper for converting arrays to images:

> arrayToImage
>   :: (MonadIO m, JP.Pixel pixel)
>   => A.IOArray (Int, Int) pixel
>   -> m (JP.Image pixel)
> arrayToImage arr = do
>   xss <- liftIO $ toList2D arr
>   ((a1,b1),(a2,b2)) <- liftIO $ A.getBounds arr
>   return $ JP.generateImage (\i j -> (xss!!i)!!j) (a2-a1) (b2-b1)



State
-----

We're nearly ready to start porting WFC -- we just need to implement the state type. Since there are only three classes carrying state, and most of the state is in one class, for simplicity's sake we'll use a single giant record type for all variables.

> data Vars pixel = Vars
>   -- Model
>   { wave :: IORef (A.IOArray (Int, Int) Bool)
> 
>   , propagator :: IORef (A.IOArray (Int, Int) [Int])
>   , compatible :: IORef (A.IOArray (Int, Int, Int) Int)
>   , observed :: IORef (A.IOArray Int Int)
> 
>   , stack :: Memory [(Int, Int)]
> 
>   , fmx :: Memory Int
>   , fmy :: Memory Int
>   , t :: Memory Int
>   , periodic :: Memory Bool
> 
>   , weights :: IORef (A.IOArray Int Double)
>   , weightLogWeights :: IORef (A.IOArray Int Double)
> 
>   , sumsOfOnes :: IORef (A.IOArray Int Int)
> 
>   , sumOfWeights :: Memory Double
>   , sumOfWeightLogWeights :: Memory Double
>   , startingEntropy :: Memory Double
> 
>   , sumsOfWeights :: IORef (A.IOArray Int Double)
>   , sumsOfWeightLogWeights :: IORef (A.IOArray Int Double)
>   , entropies :: IORef (A.IOArray Int Double)
> 
>   , onBoundary :: Memory (Int -> Int -> Bool)
> 
> 
>   , bitmapData :: IORef (A.IOArray (Int, Int) pixel)
> 
> 
>   -- OverlappingModel
>   , n :: Memory Int
>   , patterns :: IORef (A.IOArray (Int, Int) Int)
>   , colors :: Memory [pixel]
>   , ground :: Memory Int
> 
>   , contributors :: Memory Int
>   , red :: Memory Int
>   , blue :: Memory Int
>   , green :: Memory Int
> 
> 
>   -- SimpleTiledModel
>   , tiles :: Memory [pixel]
>   , tilenames :: Memory [String]
>   , tilesize :: Memory Int
>   , black :: Memory Bool
>   }

We also need a function to construct an "empty" state. These are updated with real values as the algorithm progresses.

> initializeVars :: IO (Vars pixel)
> initializeVars = do
>   wave <- array2D (0,0) True >>= newIORef
> 
>   propagator <- array2D (0,0) ([] :: [Int]) >>= newIORef
>   compatible <- array3D (0,0,0) (0 :: Int) >>= newIORef
>   observed <- array1D 0 (0 :: Int) >>= newIORef
> 
>   stack <- var ([] :: [(Int, Int)])
> 
>   fmx <- var 0
>   fmy <- var 0
>   t <- var 0
>   periodic <- var False
> 
>   sumsOfOnes <- array1D 0 (0 :: Int) >>= newIORef
> 
>   sumOfWeights <- var (0 :: Double)
>   sumOfWeightLogWeights <- var (0 :: Double)
>   startingEntropy <- var (0 :: Double)
> 
>   weights <- array1D 0 (0 :: Double) >>= newIORef
>   weightLogWeights <- array1D 0 (0 :: Double) >>= newIORef
> 
>   sumsOfWeights <- array1D 0 (0 :: Double) >>= newIORef
>   sumsOfWeightLogWeights <- array1D 0 (0 :: Double) >>= newIORef
>   entropies <- array1D 0 (0 :: Double) >>= newIORef
> 
>   onBoundary <- var (\_ _ -> False)
> 
>   bitmapData <- array2D (0,0) (error "initializeData: bitmapData") >>= newIORef
> 
>   -- OverlappingModel
>   n <- var (0 :: Int)
>   patterns <- array2D (0,0) (0 :: Int) >>= newIORef
>   colors <- var ([] :: [pixel])
>   ground <- var (0 :: Int)
> 
>   contributors <- var (0 :: Int)
>   red <- var (0 :: Int)
>   blue <- var (0 :: Int)
>   green <- var (0 :: Int)
> 
> 
>   -- SimpleTiledModel
>   tiles <- var ([] :: [pixel])
>   tilenames <- var ([] :: [String])
>   tilesize <- var (0 :: Int)
>   black <- var False
> 
>   return Vars{..}



The `Model` Class
-----------------

Next a type synonym:

> type WFC pixel a = Global (Vars pixel) a

And with that we're now prepared to actually port the code! I've tried to get as close as I can to a line-for-line translation. Each method in the original code corresponds to a Haskell function here.

First up, the constructor for `Model`. Note that with a little extra boilerplate to bring the state into scope and handle early exits, the code looks very similar to the original C#.

> construct :: Int -> Int -> WFC pixel ()
> construct width height = do
>   Vars{..} <- globals
>   liftIO $ runImp $ do
>     fmx =: width
>     fmy =: height
>     return ()

`Init()`:

> init :: WFC pixel ()
> init = do
>   v@Vars{..} <- globals
>   _fmx <- peek fmx
>   _fmy <- peek fmy
>   _t <- peek t
>   liftIO $ runImp $ do
>     wave =:: array2D (_fmx * _fmy, _t) True
>     compatible =:: array3D (_fmx * _fmy, _t, 4) 0
> 
>     weightLogWeights =:: array1D _t 0
>     arrayLoopM_ weightLogWeights $ \i -> do
>       x <- peek (weights :@ i)
>       (weightLogWeights :@ i) =: (info x)
> 
>     sumOfWeights =: 0
>     arrayLoopM_ weights $ \i -> do
>       x <- peek $ weights :@ i
>       sumOfWeights +=: x
> 
>     sumOfWeightLogWeights =: 0
>     arrayLoopM_ weightLogWeights $ \i -> do
>       w <- peek (weightLogWeights :@ i)
>       sumOfWeightLogWeights +=: w
> 
>     sw <- peek sumOfWeights
>     si <- peek sumOfWeightLogWeights
>     startingEntropy =: ((log sw) - (si / sw))
> 
>     sumsOfOnes =:: array1D (_fmx * _fmy) 0
>     sumsOfWeights =:: array1D (_fmx * _fmy) 0
>     sumsOfWeightLogWeights =:: array1D (_fmx * _fmy) 0
>     entropies =:: array1D (_fmx * _fmy) 0
> 
>     stack =: []
> 
>     return ()

Where `info` measures the information of a probability.

> info :: Double -> Double
> info 0 = 0
> info x = x * log x

`Clear()`:

> clear :: WFC pixel ()
> clear = do
>   Vars{..} <- globals
>   _fmx <- peek fmx
>   _fmy <- peek fmy
>   liftIO $ runImp $ do
>     arrayFill wave True
> 
>     arrayLoopM_ compatible $ \(i,t,d) -> do
>       ws <- peek (propagator :@ (_opposite d, t))
>       (compatible :@ (i,t,d)) =: (length ws)
> 
>     len weights >>= arrayFill sumsOfOnes
>     peek sumOfWeights >>= arrayFill sumsOfWeights
>     peek sumOfWeightLogWeights >>= arrayFill sumsOfWeightLogWeights
>     peek startingEntropy >>= arrayFill entropies
> 
>     return ()

`_opposite`:

> _opposite :: Int -> Int
> _opposite i = case i of
>   0 -> 2; 1 -> 3; 2 -> 0; 3 -> 1

`Ban()`:

> ban :: Int -> Int -> WFC pixel ()
> ban i u = do
>   v@Vars{..} <- globals
>   liftIO $ runImp $ do
>     (wave :@ (i,u)) =: False
> 
>     forLoopM [0..3] () $ \d -> do
>       (compatible :@ (i,u,d)) =: 0
>       loop
> 
>     stack .=: (i,u)
> 
>     wsum <- peek (sumsOfWeights :@ i)
>     wswlw <- peek (sumsOfWeightLogWeights :@ i)
>     (entropies :@ i) +=: (wswlw / wsum - log wsum)
> 
>     (sumsOfOnes :@ i) -=: 1
>     wt <- peek (weights :@ u)
>     (sumsOfWeights :@ i) -=: wt
> 
>     wlw <- peek (weightLogWeights :@ u)
>     (sumsOfWeightLogWeights :@ i) -=: wlw
> 
>     wsum <- peek (sumsOfWeights :@ i)
>     wswlw <- peek (sumsOfWeightLogWeights :@ i)
>     (entropies :@ i) -=: (wswlw / wsum - log wsum)
> 
>     return ()

`Propagate()`:

> propagate :: WFC pixel ()
> propagate = do
>   v@Vars{..} <- globals
>   (!_fmx) <- peek fmx
>   (!_fmy) <- peek fmy
>   (!_t) <- peek t
>   _onBoundary <- peek onBoundary
>   liftIO $ runImp $ do
>     whileLoopM (notEmptyM stack) () $ do
>       liftIO $ putStrLn $ "stack"
>       _stack <- peek stack
>       let (i1,u) = head _stack
>       liftIO $ putStrLn $ "i1 = " ++ show i1 ++ " and u = " ++ show u
>       stack =: (tail _stack)
>       let x1 = rem i1 _fmx
>       let y1 = quot i1 _fmx
> 
>       forLoopM [0..3] Loop $ \d -> do
>         let x2' = x1 + _DX d
>         let y2' = y1 + _DY d
>         liftIO $ putStrLn "d loop"
>         if _onBoundary x2' y2'
>           then continue
>           else do
>             let
>               (!x2) = wrapTo x2' _fmx
>               (!y2) = wrapTo y2' _fmy
>               (!i2) = x2 + y2 * _fmx
>             liftIO $ putStrLn "defined constants"
> 
>             p <- peek (propagator :@ (d,u))
> 
>             forLoopM p Loop $ \t2 -> do
>               liftIO $ putStrLn $ "loop over p: " ++ show p
>               liftIO $ putStrLn "what is going on?"
>               liftIO $ putStrLn $ "d = " ++ show d
>               liftIO $ putStrLn $ "t2 = " ++ show t2
>               liftIO $ putStrLn $ "i2 = " ++ show i2
>               (compatible :@ (i2,t2,d)) -=: 1
>               liftIO $ putStrLn $ "compatible at i2 = " ++ show i2 ++ " t2 = " ++ show t2 ++ " show d = " ++ show d
>               x <- peek (compatible :@ (i2,t2,d))
>               if x == 0
>                 then call v $ ban i2 t2
>                 else return ()
>               loop

Helpers:

> wrapTo :: Int -> Int -> Int
> wrapTo a n = if a < 0
>   then a + n
>   else if a >= n
>     then a - n
>     else a
> 
> _DX :: Int -> Int
> _DX i = case i of
>   0 -> -1; 1 -> 0; 2 -> 1; 3 -> 0
>   k -> error $ "_DX at " ++ show k
> 
> _DY :: Int -> Int
> _DY i = case i of
>   0 -> 0; 1 -> 1; 2 -> 0; 3 -> -1
>   k -> error $ "_DY at " ++ show k

`Observe()`:

> observe :: WFC pixel (Maybe Bool)
> observe = do
>   v@Vars{..} <- globals
>   _fmx <- peek fmx
>   _fmy <- peek fmy
>   _onBoundary <- peek onBoundary
>   _t <- peek t
>   liftIO $ runImp $ do
>     min <- var (1000 :: Double) 
>     argmin <- var (-1 :: Int)
> 
>     forLoopM [0 .. (_fmx*_fmy-1)] () $ \i -> do
>       if _onBoundary (rem i _fmx) (div i _fmx)
>         then continue
>         else do
>           amount <- peek (sumsOfOnes :@ i)
>           if amount == 0
>             then exitEarly $ Just False
>             else do
>               entropy <- peek (entropies :@ i)
>               _min <- peek min
>               if (amount > 1) && (entropy <= _min)
>                 then do
>                   noise <- liftIO $ fmap (0.000001*) $ R.randomRIO (0,1 :: Double)
>                   if entropy + noise < _min
>                     then do
>                       min =: (entropy + noise)
>                       argmin =: i
>                       loop
>                     else loop
>                 else loop
> 
>     _argmin <- peek argmin
>     if _argmin == (-1)
>       then do
>         observed =:: array1D (_fmx * _fmy) (0 :: Int)
> 
>         forLoopM [0 .. (_fmx*_fmy-1)] () $ \i -> do
>           forLoopM [0 .. (_t-1)] Loop $ \v -> do
>             p <- peek (wave :@ (i,v))
>             if p == True
>               then do
>                 (observed :@ i) =: v
>                 break Loop
>               else loop
> 
>         exitEarly $ Just True
>       else return ()
> 
>     distribution <- array1D _t (0::Double) >>= (liftIO . newIORef)
> 
>     arrayLoopM_ distribution $ \i -> do
>       p <- peek (wave :@ (_argmin,i))
>       wt <- peek (weights :@ i)
>       (distribution :@ i) =: if p then wt else 0
> 
>     r <- sampleFrom distribution
> 
>     forLoopM [0..(_t-1)] () $ \u -> do
>       p <- peek (wave :@ (_argmin, u))
>       if p /= (u == r)
>         then call v $ ban _argmin u
>         else return ()
>       loop
> 
>     return Nothing

Helper for sampling discrete distributions:

> sampleFrom
>   :: (MonadIO m, R.Random a, Num a, Fractional a, Ord a)
>   => IORef (A.IOArray Int a)
>   -> m Int
> 
> sampleFrom arr = do
>   r <- liftIO $ R.randomRIO (0,1)
>   liftIO $ runImp $ do
>     sum <- do
>       s <- arraySum arr
>       if s == 0
>         then do
>           arrayFill arr 1
>           arraySum arr
>         else return s
> 
>     arrayLoopM_ arr $ \j -> do
>       (arr :@ j) /=: sum
> 
>     x <- var 0
> 
>     arrayLoopM_ arr $ \i -> do
>       v <- peek (arr :@ i)
>       x +=: v
>       k <- peek x
>       if r <= k
>         then exitEarly i
>         else return ()
> 
>     return 0

`Run()`:

> run :: Int -> WFC pixel Bool
> run limit = do
>   v@Vars{..} <- globals
>   liftIO $ runImp $ do
>     call v init
>     liftIO $ putStrLn "init run"
>     call v overlap_clear
>     liftIO $ putStrLn "clear run"
> 
>     forLoopM [1..limit] () $ \i -> do
>       obs <- call v observe
>       liftIO $ putStrLn $ "observe call " ++ show i
>       case obs of
>         Just p -> exitEarly p
>         Nothing -> do
>           call v propagate
>           liftIO $ putStrLn "propagate run"
>           loop
> 
>     return True



The `OverlappingModel` Class
----------------------------

`Clear()`:

> overlap_clear :: WFC pixel ()
> overlap_clear = do
>   v@Vars{..} <- globals
>   _fmx <- peek fmx
>   _fmy <- peek fmy
>   _t <- peek t
>   _ground <- peek ground
>   liftIO $ runImp $ do
>     call v clear
> 
>     if _ground == 0
>       then return ()
>       else do
>         forLoopM [0 .. (_fmx - 1)] () $ \x -> do
>           forLoopM [0 .. (_t - 1)] Loop $ \s -> do
>             if s /= _ground
>               then call v $ ban (x + (_fmy - 1) * _fmx) s
>               else return ()
>             loop
>           forLoopM [0 .. (_fmy - 2)] Loop $ \y -> do
>             call v $ ban (x + y * _fmx) _ground
>             loop
>           call v propagate
>           loop

`Graphics()`:

> overlap_graphics :: WFC JP.PixelRGB8 (JP.Image JP.PixelRGB8)
> overlap_graphics = do
>   v@Vars{..} <- globals
>   _fmx <- peek fmx
>   _fmy <- peek fmy
>   _t <- peek t
>   _n <- peek n
>   _onBoundary <- peek onBoundary
>   liftIO $ runImp $ do
>     liftIO $ putStrLn "overlap_graphics"
>     bitmapData =:: array2D (_fmx, _fmy) (JP.PixelRGB8 0 0 0)
> 
>     p <- arrayIsNull observed
>     if not p
>       then do
>         liftIO $ putStrLn "not p"
>         forLoopM [0..(_fmy - 1)] () $ \y -> do
>           let dy = if y < _fmy - _n + 1 then 0 else _n - 1
>           forLoopM [0..(_fmx - 1)] Loop $ \x -> do
>             let dx = if x < _fmx - _n + 1 then 0 else _n - 1
>             h <- peek (observed :@ (x - dx + (y - dy) * _fmx))
>             k <- peek (patterns :@ (h, dx + dy * _n))
>             _colors <- peek colors
>             (bitmapData :@ (x,y)) =: (_colors !! k)
>             loop
>       else do
>         liftIO $ putStrLn "yes p"
>         forLoopM [0 .. (_fmx*_fmy - 1)] () $ \i -> do
>           let x = i `mod` _fmx
>           let y = i `div` _fmx
>           liftIO $ putStrLn $ "(x,y) = " ++ show (x,y)
>           contributors =: 0
>           red =: 0
>           blue =: 0
>           green =: 0
>           forLoopM [0..(_n-1)] Loop $ \dy -> do
>             forLoopM [0..(_n-1)] Loop $ \dx -> do
>               let sx' = x - dx
>               let sx = if sx' < 0 then sx' + _fmx else sx'
>               let sy' = y - dy
>               let sy = if sy' < 0 then sy' + _fmy else sy'
>               liftIO $ putStrLn $ "(sx,sy) = " ++ show (sx,sy)
>               let s = sx + sy * _fmx
>               if _onBoundary sx sy
>                 then continue
>                 else do
>                   forLoopM [0..(_t-1)] Loop $ \u -> do
>                     liftIO $ putStrLn $ "u = " ++ show u
>                     liftIO $ putStrLn $ "s = " ++ show s
>                     liftIO $ readIORef wave >>= A.getBounds >>= (putStrLn . show)
>                     p <- peek (wave :@ (s,u))
>                     liftIO $ putStrLn $ "p = " ++ show p
>                     if p
>                       then do
>                         contributors +=: 1
>                         _contributors_debug <- peek contributors
>                         liftIO $ putStrLn $ "contributors = " ++ show _contributors_debug
>                         liftIO $ putStrLn $ "(u, dx + dy * _n) = " ++ show (u, dx + dy * _n)
>                         liftIO $ readIORef patterns >>= A.getBounds >>= (putStrLn . show)
>                         w <- peek (patterns :@ (u, dx + dy * _n))
>                         liftIO $ putStrLn "patterns ok"
>                         _colors <- peek colors
>                         let JP.PixelRGB8 r g b = _colors !! w
>                         red +=: fromIntegral r
>                         blue +=: fromIntegral b
>                         green +=: fromIntegral g
>                         loop
>                       else loop
>           _contributors <- peek contributors
>           _r <- peek red
>           _b <- peek blue
>           _g <- peek green
>           liftIO $ putStrLn $ "(r,b,g) = " ++ show (_r,_b,_g)
>           liftIO $ putStrLn $ "contributors = " ++ show _contributors
>           (bitmapData :@ (x,y)) =: JP.PixelRGB8
>             (fromIntegral $ if _contributors == 0 then 0 else div _r _contributors)
>             (fromIntegral $ if _contributors == 0 then 0 else div _b _contributors)
>             (fromIntegral $ if _contributors == 0 then 0 else div _g _contributors)
>           loop
>     arr <- liftIO $ readIORef bitmapData
>     arrayToImage arr

`onBoundary()`:

> overlap_onBoundary :: (Int,Int,Int,Bool) -> Int -> Int -> Bool
> overlap_onBoundary (_fmx, _fmy, _n, _periodic) x y =
>   (not _periodic) && or
>     [ x + _n > _fmx, y + _n > _fmy, x < 0, y < 0 ]

`OverlappingModel()`:

> overlap_construct
>   :: String -> Int -> Int -> Int -> Bool -> Bool -> Int -> Int -> WFC JP.PixelRGB8 ()
> overlap_construct name _n width height periodicInput periodicOutput symmetry _ground = do
>   v@Vars{..} <- globals
>   liftIO $ runImp $ do
>     call v $ construct width height
>     n =: _n
>     periodic =: periodicOutput
> 
>     rawPng <- liftIO $ B.readFile name
>     JP.ImageRGB8 bitmap <- case JP.decodePng rawPng of
>       Left err -> liftIO $ do
>         putStrLn err
>         exitFailure
>       Right img -> return img
>     let _smx = JP.imageWidth bitmap
>     let _smy = JP.imageHeight bitmap
> 
>     sample <- liftIO $ array2D (_smx, _smy) (0 :: Int) >>= newIORef
>     colors =: []
> 
>     forLoopM [0 .. (_smy-1)] () $ \y -> do
>       forLoopM [0 .. (_smx-1)] Loop $ \x -> do
>         let color = JP.pixelAt bitmap x y
>         i <- var (0 :: Int)
>         _colors <- peek colors
>         forLoopM _colors Loop $ \c -> do
>           if c == color
>             then break Loop
>             else do
>               i +=: 1
>               loop
>         _i <- peek i
>         if _i == length _colors
>           then colors .=: color
>           else return ()
>         (sample :@ (x,y)) =: _i
>         loop
> 
>     _C <- peek colors >>= (return . length)
>     let _W = _C ^ (_n * _n)
> 
>     let
>       patternFromSample :: (MonadIO m) => Int -> Int -> m (IORef (A.IOArray Int Int))
>       patternFromSample x y =
>         pattern _n $ \dx dy ->
>           peek (sample :@ ((x+dx) `mod` _smx, (y+dy) `mod` _smy))
> 
>       rotate :: (MonadIO m) => IORef (A.IOArray Int Int) -> m (IORef (A.IOArray Int Int))
>       rotate p =
>         pattern _n $ \x y ->
>           peek (p :@ (_n - 1 - y + x*_n))
> 
>       reflect :: (MonadIO m) => IORef (A.IOArray Int Int) -> m (IORef (A.IOArray Int Int))
>       reflect p =
>         pattern _n $ \x y ->
>           peek (p :@ (_n - 1 - x + y*_n))
> 
>       index :: (MonadIO m) => IORef (A.IOArray Int Int) -> m Int
>       index p = do
>         result <- var (0 :: Int)
>         power <- var (1 :: Int)
>         l <- len p
>         forLoopM [0 .. (l-1)] () $ \i -> do
>           q <- peek (p :@ (l - 1 - i))
>           _power <- peek power
>           result +=: (q * _power)
>           power *=: _C
>           loop
>         peek result
> 
>       patternFromIndex :: (MonadIO m) => Int -> m (IORef (A.IOArray Int Int))
>       patternFromIndex ind = do
>         residue <- var ind
>         power <- var _W
>         result <- liftIO $ array1D (_n * _n) 0 >>= newIORef
>         arrayLoopM_ result $ \i -> do
>           power //=: _C
>           count <- var (0 :: Int)
>           _power <- peek power
>           whileLoopM (residue >=: _power) () $ do
>             residue -=: _power
>             count +=: 1
>             loop
>           _count <- peek count
>           (result :@ i) =: _count
>         return result
> 
>     the_weights <- var (HM.empty :: HM.HashMap Int Int)
>     ordering <- var ([] :: [Int])
> 
>     forLoopM [0 .. if periodicInput then _smy - 1 else _smy - _n] () $ \y -> do
>       forLoopM [0 .. if periodicInput then _smx - 1 else _smx - _n] Loop $ \x -> do
> 
>         ps0 <- patternFromSample x y
>         ps1 <- reflect ps0
>         ps2 <- rotate ps0
>         ps3 <- reflect ps2
>         ps4 <- rotate ps2
>         ps5 <- reflect ps4
>         ps6 <- rotate ps4
>         ps7 <- reflect ps6
> 
>         let
>           ps u = case u of
>             0 -> ps0; 1 -> ps1; 2 -> ps2; 3 -> ps3;
>             4 -> ps4; 5 -> ps5; 6 -> ps6; 7 -> ps7;
>             k -> error $ "ps at " ++ show k
> 
>         forLoopM [0 .. (symmetry - 1)] Loop $ \k -> do
>           ind <- index (ps k)
>           _the_weights <- peek the_weights
>           if HM.member ind _the_weights
>             then do
>               the_weights =: (HM.adjust (+1) ind _the_weights)
>             else do
>               the_weights =: (HM.insert ind 1 _the_weights)
>               ordering .=: ind
>           loop
> 
>     _t <- peek the_weights >>= (return . HM.size)
>     t =: _t
>     ground =: ((_ground + _t) `mod` _t)
> 
>     patterns =:: array2D (_t, _n * _n) (0 :: Int)
>     weights =:: array1D _t (0 :: Double)
> 
>     counter <- var (0 :: Int)
>     _ordering <- peek ordering
>     forLoopM _ordering () $ \w -> do
>       _counter <- peek counter
>       arr <- patternFromIndex w
>       arrayLoopM_ arr $ \i -> do
>         z <- peek (arr :@ i)
>         (patterns :@ (_counter, i)) =: z
>       q <- peek the_weights >>= (return . HM.lookup w)
>       case q of
>         Nothing -> liftIO $ do
>           putStrLn $ "Error: the_weights lookup"
>           exitFailure
>         Just s -> do
>           (weights :@ _counter) =: (fromIntegral s)
>           counter +=: 1
>           loop
> 
>     let
>       agrees :: (MonadIO m) => IORef (A.IOArray Int Int) -> IORef (A.IOArray Int Int) -> Int -> Int -> m Bool
>       agrees p1 p2 dx dy = liftIO $ runImp $ do
>         let
>           xmin = if dx < 0 then 0 else dx
>           xmax = if dx < 0 then dx + _n else _n
>           ymin = if dy < 0 then 0 else dy
>           ymax = if dy < 0 then dy + _n else _n
>         forLoopM [ymin .. (ymax-1)] () $ \y -> do
>           forLoopM [xmin .. (xmax-1)] Loop $ \x -> do
>             q1 <- peek (p1 :@ (x + _n*y))
>             q2 <- peek (p2 :@ (x - dx + _n*(y - dy)))
>             if q1 /= q2
>               then exitEarly False
>               else loop
>         return True
> 
>     propagator =:: array2D (4,_t) ([] :: [Int])
>     forLoopM [0 .. 3] () $ \d -> do
>       forLoopM [0 .. (_t - 1)] Loop $ \t1 -> do
>         list <- var ([] :: [Int])
>         forLoopM [0 .. (_t - 1)] Loop $ \t2 -> do
>           p1 <- liftIO $ array1D (_n * _n) (0 :: Int) >>= newIORef
>           arrayLoopM_ p1 $ \i -> do
>             z <- peek (patterns :@ (t1,i))
>             (p1 :@ i) =: z
>           p2 <- liftIO $ array1D (_n * _n) (0 :: Int) >>= newIORef
>           arrayLoopM_ p2 $ \i -> do
>             z <- peek (patterns :@ (t2,i))
>             (p2 :@ i) =: z
>           q <- agrees p1 p2 (_DX d) (_DY d)
>           if q
>             then list .=: t2
>             else return ()
>           ls <- peek list
>           liftIO $ putStrLn $ "ls = " ++ show ls
>           (propagator :@ (d,t1)) =: ls
>           loop
> 
>     onBoundary =: overlap_onBoundary (width, height, _n, periodicOutput)
> 
>     return ()

`pattern()`:

> pattern :: (MonadIO m) => Int -> (Int -> Int -> m Int) -> m (IORef (A.IOArray Int Int))
> pattern _n f = do
>   result <- liftIO $ array1D (_n * _n) 0 >>= newIORef
>   forLoopM [0 .. (_n-1)] () $ \y -> do
>     forLoopM [0 .. (_n-1)] Loop $ \x -> do
>       z <- f x y
>       (result :@ (x + y*_n)) =: z
>       loop
>   return result




> testing :: IO ()
> testing = do
>   putStrLn "starting"
>   v <- initializeVars
>   putStrLn "vars initialized"
>   call v $ overlap_construct "RedMaze.png" 3 48 48 True False 2 0
>   putStrLn "constructor run"
>   _ <- call v $ run 5000
>   putStrLn "run run"
>   img <- call v $ overlap_graphics
>   putStrLn "graphics run"
>   JP.savePngImage "FlowersOut.png" (JP.ImageRGB8 img)






> main :: IO ()
> main = testing


