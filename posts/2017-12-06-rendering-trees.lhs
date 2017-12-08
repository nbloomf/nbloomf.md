---
title: Rendering Trees
author: nbloomf
date: 2017-12-06
tags: literate-haskell
---

Recently a colleague of mine wrote some documentation that included a sample directory listing rendered in plain text, something like this:

```
foo
├─ bar
│  └─ quux
└─ baz
```

Let's figure out how to do this from scratch. 

> {-# LANGUAGE LambdaCase #-}
> module RenderingTrees where
> 
> import Data.List
> import System.Environment
> import System.Directory.Tree
> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Lisp
> import Text.XML.HXT.Core hiding (Tree)
> import Data.Tree.NTree.TypeDefs

A directory listing is a multi-way tree, sometimes called a *rose tree*. We can define such trees recursively like so.

> data Tree a
>   = T a [Tree a]
>   deriving Show

For example, here's some trees.

> tA, tB, tC, tD, tE :: Tree String
> tA = T "A" []
> tB = T "B" [tA]
> tC = T "C" [tA, tB]
> tD = T "D" [tA, tB, tC]
> tE = T "E" [tA, tB, tC, tD]
> tF = T "F" [tA, tB, tC, tD, tE]
> 
> fib :: Integer -> Tree Integer
> fib 0 = T 0 []
> fib 1 = T 1 []
> fib k = T k [fib (k-1), fib (k-2)]

The ``Tree`` type is functorial.

> instance Functor Tree where
>   fmap f (T x bs) = T (f x) (map (fmap f) bs)

We can serialize a tree depth-first:

> flatten :: Tree a -> [a]
> flatten (T x bs) = x : concatMap flatten bs

And a ``Tree String`` can be rendered just by printing the nodes one per line, in depth-first order.

> render :: Tree String -> String
> render = concat . intersperse "\n" . flatten

``render`` *kind of* does what we want -- just without the nice line art along the left side.

```haskell
$> putStrLn $ render tD
D
A
B
A
C
A
B
A
```

So now to append the right prefix to each line. ``Tree`` is a recursive type, so let's think recursively. We can imagine rendering the child branches of a node, then appending a prefix to each line depending on whether that line is an immediate child node, the *last* immediate child node, a descendant of a child node, or a descendant of the last child node.

We need to map over the list of branches, applying a different map to the last element:

> mapLast :: (a -> b) -> (a -> b) -> [a] -> [b]
> mapLast f g = \case
>   []   -> []
>   x:[] -> [g x]
>   x:xs -> (f x) : mapLast f g xs

And we need to map over a tree, applying a different map to the root:

> mapRoot :: (a -> b) -> (a -> b) -> Tree a -> Tree b
> mapRoot f g (T x bs) = T (f x) (map (fmap g) bs)

With that, adding prefixes works like so.

> addPrefix :: Tree String -> Tree String
> addPrefix (T x bs) = T x $ mapLast
>   (mapRoot ("├─ " ++) ("│  " ++))
>   (mapRoot ("└─ " ++) ("   " ++))
>   (map addPrefix bs)

For example:

```haskell
$> putStrLn $ render $ addPrefix tD
D
├─ A
├─ B
│  └─ A
└─ C
   ├─ A
   └─ B
      └─ A
```

woo

For fun, let's define a helper:

> pretty :: Tree String -> String
> pretty = render . addPrefix


directory listings, why not
---------------------------

The ``System.Directory.Tree`` library module has some functions for getting the *tree* structure of a *directory* on the *system*. We'll need to convert the native tree type of that library to our ``Tree``:

> dir :: DirTree a -> Tree String
> dir (Failed path _) = T path []
> dir (Dir path xs) = T path (map dir xs)
> dir (File path _) = T path []

blah blah

> theDirTree :: FilePath -> IO ()
> theDirTree path = do
>   (_ :/ dtree) <- readDirectory path
>   putStrLn $ pretty $ dir $ sortDir dtree


s-expressions because sure
--------------------------

The ``Text.ParserCombinators.Parsec.Lisp`` library module has some functions for parsing lisp code, a.k.a. S-expressions. We'll need to convert the native tree type of that library to our ``Tree``:

> lisp :: LispVal -> Tree String
> lisp (Atom str) = T str []
> lisp (List xs) = T "()" (map lisp $ xs ++ [Atom "nil"])
> lisp (DottedList xs y) = T "()" (map lisp $ xs ++ [y])
> lisp (Number k) = T (show k) []
> lisp (String str) = T (show str) []
> lisp (Bool True) = T "#t" []
> lisp (Bool False) = T "#f" []

frou frou

> theLispTree :: String -> IO ()
> theLispTree str =
>   case parse parseExpr "" str of
>     Left err -> putStrLn $ show err
>     Right t -> putStrLn $ pretty $ lisp t

for example:

```haskell
$> theLispTree "(foo bar (quux xyzzy) baz)"
()
├─ foo
├─ bar
├─ ()
│  ├─ quux
│  ├─ xyzzy
│  └─ nil
├─ baz
└─ nil
```


html, ok
-------

The HXT library can parse arbitrary XML into rose trees. With some glue code we can render those too.

> xmlTree :: NTree a -> Tree a
> xmlTree (NTree x ts) = T x (map xmlTree ts)
> 
> xml :: NTree XNode -> Tree String
> xml = fmap fromNode . xmlTree
> 
> fromNode :: XNode -> String
> fromNode = \case
>   XText str -> str
>   XBlob blob -> blobToString blob
>   XCharRef k -> "char: " ++ show k
>   XEntityRef str -> str
>   XCmt str -> str
>   XCdata str -> str
>   XPi name _ -> show name
>   XTag name attr -> show name
>   XDTD dtd _ -> show dtd
>   XAttr name -> show name
>   XError _ msg -> msg

and...

> theHTMLTree :: String -> IO ()
> theHTMLTree str = do
>   ts <- runX
>           $ readString [withParseHTML yes, withValidate no]
>           $ filter (/= '\n') str
>   sequence_ $ map (putStrLn . pretty . xml) ts

such as

```haskell
$> theHTMLTree "<html><head><title>a thing</title></head><body><p>wut</p></body></html>"
"/"
└─ "html"
   ├─ "head"
   │  └─ "title"
   │     └─ a thing
   └─ "body"
      └─ "p"
         └─ wut
```


the end
-------

Finally a ``main`` function so we can use this from the command line. 

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     ["--path",path] -> theDirTree path
>     ["--lisp"] -> getContents >>= theLispTree
>     ["--html"] -> getContents >>= theHTMLTree
>     _ -> do
>       putStrLn "Usage:"
>       putStrLn "  rendering-trees --path PATH : print listing for PATH"
>       putStrLn "  rendering-trees --lisp      : print lisp file on stdin"
>       putStrLn "  rendering-trees --html      : print html file on stdin"

fun fun
