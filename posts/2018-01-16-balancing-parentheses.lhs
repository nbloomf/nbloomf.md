---
title: Balancing Parentheses
author: nbloomf
date: 2018-01-16
tags: literate-haskell
---

> module BalanceDelimiters where
> 
> import Data.List
> import Data.Tuple
> import Control.Monad
> 
> import System.Exit
> import System.Environment
> import System.Console.GetOpt

Let's make a tool to find unbalanced parentheses.

What does it mean for the parentheses in a string to be balanced? We could come up with a recursive definition, like

1. If $u$ does not contain either `'('` or `')'`, then $u$ is balanced;
2. If $u$ is balanced, then $(u)$ is balanced; and
3. If $u$ and $v$ are balanced, then $uv$ is balanced.

We can use these rules to construct balanced strings one step at a time. For example,

* `"a"` is balanced (rule 1)
* `""` is balanced (rule 1)
* `"()"` is balanced (rule 2, $u = \texttt{""}$)
* `"a()"` is balanced (rule 3, $u = \texttt{"a"}$ and $v = \texttt{"()"}$)
* `"(a())"` is balanced (rule 2, $u = \texttt{"a()"}$)
* ...

But what if we want to *detect* balanced strings? We can do that with a stack. Consume the first character (or "token") of the string; if it is an open parenthesis, push it onto the stack; if it is a closing parenthesis try to pop a previously pushed opening parenthesis off of the stack (if we can't, there's a closing paren with no opening paren); if it is neither, throw it away. Recurse on the remainder of the string until it is empty. If the stack is not empty at the end, there is an opening paren with no closing paren.

The pattern here matches a fold over the input string, taken as a list of tokens. We generalize the process of consuming a single character slightly as ``checkToken1``; this map takes (1) a pair represening the opening and closing tokens, (2) a stack, and (3) a single token, and returns an updated stack. The return type is a `Maybe` to account for the failure case where we attempt to pop an empty stack.

> checkToken1 :: (Eq a) => (a,a) -> [a] -> a -> Maybe [a]
> checkToken1 (open,close) stack token =
>   if token == open
>     then Just (open:stack)
>     else if token == close
>       then case stack of
>         [] -> Nothing
>         (w:ws) -> if open == w then Just ws else Just stack
>       else Just stack

Wrapping `checkToken1` in a monadic fold, with an empty stack as the base value, we can balance strings.

> balance1 :: (Eq a) => (a,a) -> [a] -> Maybe [a]
> balance1 ds = foldM (checkToken1 ds) []

For example:

```haskell
$> balance1 ('(',')') "hello world"
Just ""
$> balance1 ('(',')') "hello w(orld"
Just "("
$> balance1 ('(',')') "hello w(or)ld"
Just ""
$> balance1 ('(',')') "hello w(or)l)d"
Nothing
$> balance1 ('(',')') "hell(o w(or)l)d"
Just ""
```

Note the two different failure cases. `Nothing` means we have an unbalanced closing paren, and `Just (_:_)` means we have an unbalanced opening paren.

Neat!

But can we do better? This program has some weaknesses that make it less than ideal for my needs.

1. It can only handle one set of delimiters. In practice, text will have delimiters of several kinds, which can be nested inside each other. For instance, we'd like `"(){}"` to be balanced, as well as `"({})"`, but not `"({)}"`.
2. It can only handle delimiters consisting of a single character, at least, not without tokenizing the input string first.
3. It can only tell us whether an unbalanced delimiter exists; it doesn't tell us where it is.

It won't take much to beef up `balance1` to handle these issues.

First, let's deal with the problem of specifying locations in text. I can think of two basic scenarios: (1) we have a single line of text and want to specify the column number of a single character, and (2) we have several lines of text and want to specify the line and column numbers of a single character.

In the first case, we want to turn a `[a]` into something like `[(a,Int)]`. The standard `zip` can handle this.

> num :: [a] -> [(a,Int)]
> num xs = zip xs [1..]

Thinking of `[a]` as a list of graphemes, `num` just attaches each grapheme to its index in the list.

```haskell
$> num "hello"
[('h',1),('e',2),('l',3),('l',4),('o',5)]
```

In the second case, we want to turn a `[[a]]` into something like `[(a,(Int,Int))]`. This is a little more complicated (but not much).

> lineCol :: [[a]] -> [(a,(Int,Int))]
> lineCol xss = concatMap (\(xs,i) -> map (\(x,j) -> (x,(i,j))) xs) $ num (map num xss)

```haskell
$> lineCol ["hello","world"]
[('h',(1,1)),('e',(1,2)),('l',(1,3)),('l',(1,4)),('o',(1,5))
,('w',(2,1)),('o',(2,2)),('r',(2,3)),('l',(2,4)),('d',(2,5))]
```

In general, we'd like to balance a string against a set of pairs of delimiting *substrings*. To do this with a strategy like `balance1` we'll need to tokenize the input stream. In this simplified model, our delimiting substrings are tokens, as are any single characters that are not at the head of a delimiting substring. For example, if we're balancing the delimiters `(`, `)`, `<<`, and `>>`, then the string

    (hey<<woo>)

should tokenize as

    '(' 'h' 'e' 'y' '<<' 'w' 'o' 'o' '>' ')'

The usual way to do this is to check, for each delimiter, whether it is a prefix of the input stream, and if so, strip it away. Note that our input stream comes equipped with location data, so it will have type `[(a,t)]` for some location type `t`, while the delimiter tokens each have type `[a]`. The `stripPrefixMap` function will detect and remove prefix tokens. Note the return type; `Nothing` means the given token was not a prefix, and `Just bs` returns the remainder of the input after the token is removed.

> stripPrefixMap :: (Eq a) => (b -> a) -> [a] -> [b] -> Maybe [b]
> stripPrefixMap f x y = case x of
>   [] -> Just y
>   (a:as) -> case y of
>     [] -> Nothing
>     (b:bs) -> if a == (f b)
>       then stripPrefixMap f as bs
>       else Nothing

Next, `stripToken` takes a list of tokens and an input stream, and returns either a pair consisting of the first token (and the location of its first grapheme) and the remainder of the input stream, or nothing if the input stream is empty.

> stripToken :: (Eq a) => [[a]] -> [(a,t)] -> Maybe (([a],t), [(a,t)])
> stripToken tokens stream = case stream of
>   [] -> Nothing
>   ((x,u):zs) -> case tokens of
>     [] -> Just (([x],u), zs)
>     (t:ts) -> case stripPrefixMap fst t stream of
>       Nothing -> stripToken ts stream
>       Just ws -> Just ((t,u), ws)

Finally, `stripToken` has the appropriate type so that `tokenize` is an `unfoldr`.

> tokenize :: (Eq a) => [[a]] -> [(a,t)] -> [([a],t)]
> tokenize ts = unfoldr (stripToken ts)

```haskell
$> tokenize ["(",")"] (num "hi(woo)")
[("h",1),("i",2),("(",3),("w",4),("o",5),("o",6),(")",7)]
$> tokenize ["<<","&&"] (num "<hi&&k<<")
[("<",1),("h",2),("i",3),("&&",4),("k",6),("<<",7)]
```

Now the old `checkToken1` only nees a couple of adaptations to work on multiple delimiters. The failure cases are a little more complicated; now we can have a close with no open, an open with no close, or a close with a mismatched open.

> checkToken :: (Eq a)
>   => [(a,a)] -> [(a,t)] -> (a,t) -> Either (Either (a,t) ((a,t),(a,t))) [(a,t)]
> checkToken ds z (x,t) =
>   case lookup x ds of
>     Just y -> Right ((x,t):z) -- opening delimiter found
>     Nothing -> case lookup x (map swap ds) of
>       Just y -> case z of -- closing delimiter found
>         [] -> Left (Left (x,t)) -- close with no open
>         ((w,u):ws) -> if w == y
>           then Right ws
>           else Left (Right ((x,t),(w,u))) -- close with mismatched open
>       Nothing -> Right z

The shape of `checkToken` is right for `foldM`.

> balance :: (Eq a) => [(a,a)] -> [(a,t)] -> Either (Either (a,t) ((a,t),(a,t))) [(a,t)]
> balance ds = foldM (checkToken ds) []

And a helper to turn our list of paired delimiters into a list of tokens:

> flat :: [(a,a)] -> [a]
> flat [] = []
> flat ((a,b):xs) = a:b:(flat xs)

```haskell
$> let ds = [("(",")"),("<<",">>")]
$> balance ds $ tokenize (flat ds) $ num "hello"
Right []
$> balance ds $ tokenize (flat ds) $ num "hello("
Right [("(",6)]
$> balance ds $ tokenize (flat ds) $ num "hel)lo"
Left (Left (")",4))
$> balance ds $ tokenize (flat ds) $ num "h(e)llo"
Right []
$> balance ds $ tokenize (flat ds) $ num "h<<ello"
Right [("<<",2)]
$> balance ds $ tokenize (flat ds) $ num "h<<el)lo"
Left (Right ((")",6),("<<",2)))
```

Again, note the three different failure cases. We'll wrap this behind a function.

> balanceDelimiters :: (Eq a)
>   => [([a],[a])]  -- paired delimiters
>   -> [(a,t)]      -- stream of graphemes with location data
>   -> Either (Either ([a],t) (([a],t),([a],t))) [([a],t)]
> balanceDelimiters ds = balance ds . tokenize (flat ds)

Now to wire this function into the shell. Before we can do this, two questions need answers.

1. Should we balance the entire input, or balance each line separately? We'll use a flag to toggle this, with "entire input" as the default.
2. What delimiters should we balance? We'll use an optional parameter to set this, with a reasonable default.

We'll use a type to represent these options.

> data Flags = Flags
>   { lineMode  :: Bool
>   , delimiter :: [(String,String)]
>   } deriving Show
> 
> defaultFlags :: Flags
> defaultFlags = Flags
>   { lineMode  = False
>   , delimiter = [("(",")"),("{","}"),("[","]")]
>   }

We'll use the `GetOpt` library to handle parsing command line options.

> options :: [OptDescr (Flags -> Maybe Flags)]
> options =
>   [ Option ['l'] ["line"]
>       (NoArg (\opts -> Just $ opts { lineMode = True }))
>       "balance each input line separately"
> 
>   , Option ['d'] ["delimiters"]
>       (ReqArg readDelimiters "STR")
>       "delimiter pairs, as a space-delimited string"
>   ]
>   where
>     readDelimiters str opts = do
>       ds <- readPairs (words str)
>       return $ opts { delimiter = ds }
> 
>     readPairs :: [String] -> Maybe [(String,String)]
>     readPairs z = case z of
>       [] -> Just []
>       [_] -> Nothing
>       (x:y:xs) -> fmap ((x,y):) $ readPairs xs

Now `balanceFile` handles checking entire files...

> balanceFile :: FilePath -> [(String, String)] -> String -> IO ()
> balanceFile path ds text =
>   case balanceDelimiters ds (fileLoc text) of
>     Left (Left (d,t)) -> do
>       putStrLn $ path ++ ": " ++ err t
>       putStrLn $ "unbalanced closing delimiter '" ++ d ++ "'"
>       exitFailure
>     Left (Right ((d,t),(e,u))) -> do
>       putStrLn $ path ++ ": " ++ err t
>       putStrLn $ "closing delimiter '" ++ d ++ "'"
>       putStrLn $ "does not match opening '" ++ e ++ "'"
>       putStrLn $ "at " ++ err u
>       exitFailure
>     Right ((d,t):_) -> do
>       putStrLn $ path ++ ": " ++ err t
>       putStrLn $ "unbalanced opening delimiter '" ++ d ++ "'"
>       exitFailure
>     Right [] -> return ()
>   where
>     err (i,j) = "line " ++ show i ++ " column " ++ show j
> 
> 
> fileLoc :: String -> [(Char,(Int,Int))]
> fileLoc str = unfoldr foo (str,(1,1))
>   where
>     foo :: ([Char],(Int,Int)) -> Maybe ((Char,(Int,Int)), ([Char],(Int,Int)))
>     foo (str,(row,col)) = case str of
>       [] -> Nothing
>       (c:cs) -> if c == '\n'
>         then Just ((c,(row,col)),(cs,(row+1,1)))
>         else Just ((c,(row,col)),(cs,(row,col+1)))

...and `balanceLines` handles checking each line separately.

> balanceLines :: FilePath -> [(String, String)] -> [String] -> IO ()
> balanceLines path ds = sequence_ . zipWith (balanceLine path ds) [1..]
> 
> balanceLine :: FilePath -> [(String, String)] -> Int -> String -> IO ()
> balanceLine path ds k text = do
>   case balanceDelimiters ds (num text) of
>     Left (Left (d,t)) -> do
>       putStrLn $ path ++ ", line " ++ show k ++ ": " ++ err t
>       putStrLn $ "unbalanced closing delimiter '" ++ d ++ "'"
>       exitFailure
>     Left (Right ((d,t),(e,u))) -> do
>       putStrLn $ path ++ ", line " ++ show k ++ ": " ++ err t
>       putStrLn $ "closing delimiter '" ++ d ++ "'"
>       putStrLn $ "does not match opening '" ++ e ++ "'"
>       putStrLn $ "at " ++ err u
>       exitFailure
>     Right ((d,t):_) -> do
>       putStrLn $ path ++ ", line " ++ show k ++ ": " ++ err t
>       putStrLn $ "unbalanced opening delimiter '" ++ d ++ "'"
>       exitFailure
>     Right [] -> return ()
>   where
>     err :: Int -> String
>     err j = "column " ++ show j

And `main`:

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   let
>     argErr =
>       putStr $ usageInfo "options" options
> 
>   -- read command line arguments
>   (flag, filenames) <- case getOpt Permute options args of
>       (opts, rest, []) -> case foldl (>>=) (Just defaultFlags) opts of
>         Nothing -> argErr >> exitFailure
>         Just fs -> return (fs, rest)
>       otherwise -> argErr >> exitFailure
> 
>   let ds = delimiter flag
> 
>   case (lineMode flag, filenames) of
>     -- use stdin
>     (False, []) -> do
>       getContents >>= balanceFile "stdin" ds
> 
>     (False, _) -> do
>       let process name = readFile name >>= balanceFile name ds
>       sequence_ $ map process filenames
> 
>     (True, []) -> do
>       (fmap lines getContents) >>= balanceLines "stdin" ds
> 
>     (True, _) -> do
>       let process name = (fmap lines $ readFile name) >>= balanceLines name ds
>       sequence_ $ map process filenames
> 
>   return ()
