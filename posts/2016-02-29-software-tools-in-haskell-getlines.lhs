---
title: Software Tools in Haskell: getlines
subtitle: extract lines from stdin by index
date: 2016-02-29
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-02-29-software-tools-in-haskell-getlines.lhs) into GHCi and play along. As usual, we start with some imports.

> -- getlines: extract lines from stdin by index
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import Data.List (isPrefixOf, unfoldr, intercalate)
> import System.IO (hPutStrLn, stderr)

This program is not an example from *Software Tools*; I wrote it to test some functionality that will eventually go into the print program -- namely, parsing sets of integers.

``getlines`` does one thing: it takes a set of integers as an argument, and extracts from ``stdin`` the lines whose indices (counting from 1) are in the given set. For instance,

    getlines "6"

extracts the line at index 6. We can also specify ranges, like

    getlines "1-5"

which extracts lines 1, 2, 3, 4, and 5, as well as skip counts, like

    getlines "2+3"

which extracts every third line starting with the second (i.e. 2, 5, 8, and so on). We can give several rules separated by commas, and the indices specified will be extracted in order. So

    getlines "7-9,1,2"

will extract lines 1, 2, 7, 8, and 9, in that order. We can give more than one integer set argument, and each will be considered in turn with the results concatenated. So

    getlines "1,2" "1,2" "1,2"

extracts lines 1, 2, 1, 2, 1, and 2, in that order.

We define a data type for each kind of integer set: single integers, ranges, and skip counts.

> data IntSet
>   = Single Int
>   | Range  Int Int
>   | Skip   Int Int
>   deriving (Show)
> 
> inIntSet :: Int -> [IntSet] -> Bool
> inIntSet k ms = or $ map (inIntSet' k) ms
>   where
>     inIntSet' :: Int -> IntSet -> Bool
>     inIntSet' k (Single m)  = k == m
>     inIntSet' k (Range a b) = (a <= k) && (k <= b)
>     inIntSet' k (Skip a b)  = (k >= a) && ((k-a)`rem`b == 0)
> 
> readIntSet :: String -> Maybe (Int -> Bool)
> readIntSet xs = do
>   cs <- readIntSet' xs
>   return (\k -> inIntSet k cs)
>   where
>     readIntSet' :: String -> Maybe [IntSet]
>     readIntSet' = sequence . map oneIntSeq . breakAt ','
>       where
>         oneIntSeq :: String -> Maybe IntSet
>         oneIntSeq "" = Nothing
>         oneIntSeq xs = case readDecimalNat xs of
>           Just k  -> Just $ Single k
>           Nothing -> case map readDecimalNat $ breakAt '-' xs of
>             [Just a, Just b] -> Just $ Range a b
>             otherwise        -> case map readDecimalNat $ breakAt '+' xs of
>               [Just a, Just b] -> Just $ Skip a b
>               otherwise        -> Nothing
> 
>         breakAt :: (Eq a) => a -> [a] -> [[a]]
>         breakAt x = breakBy (== x)
>           where
>             breakBy :: (a -> Bool) -> [a] -> [[a]]
>             breakBy _ [] = [[]]
>             breakBy p xs = case break p xs of
>               (ys,[])   -> [ys]
>               (ys,_:zs) -> ys : breakBy p zs

The helper function ``readIntSet`` takes the string representation of a set and returns a function that detects whether a given integer is in the set specified. Compared to representing a set of integers as a set, this makes representing large ranges more efficient and makes representing infinite sets (like skip lists) possible.

Next we write a helper function that extracts items from a list.

> getEltsByIndex :: (Int -> Bool) -> [a] -> [a]
> getEltsByIndex p xs = map snd $ filter (p . fst) $ zip [1..] xs

We introduced the type of ASA carriage control lines in the overstrike tool. To handle such files here, we need a helper function for reading carriage control formatted lines.

> readCCLines :: String -> Maybe [CCLine]
> readCCLines = unfoldrMaybe readFirstCCLine . getLines
>   where
>     readFirstCCLine :: [String] -> Maybe (Maybe (CCLine, [String]))
>     readFirstCCLine [] = Just Nothing
>     readFirstCCLine ((' ':cs):ds) = do
>       let
>         (us,vs) = span (isPrefixOf "+") ds
> 
>         stripPlus xs = case xs of
>           '+':ys    -> Just ys
>           otherwise -> Nothing
> 
>       case sequence $ map stripPlus us of
>         Just ws -> Just (Just (CCLine $ cs:ws, vs))
>         Nothing -> Nothing
>     readFirstCCLine _ = Nothing

Finally, the main program is simple enough. We take one optional argument, ``--asacc``, which interprets "lines" using the ASA carriage control format.

> data Mode = Lines | ASACC
> 
> main :: IO ()
> main = do
>   args <- getArgs
> 
>   -- interpret arguments
>   (mode,inv,tests) <- do
>     let
>       (modeflag,rest') = case args of
>         ("--asacc":zs) -> (ASACC, zs)
>         zs             -> (Lines, zs)
> 
>       (notflag,rest) = case rest' of
>         ("--not":zs) -> (True,  zs)
>         zs           -> (False, zs)
> 
>     ps <- case sequence $ map readIntSet rest of
>       Just xs -> return xs
>       Nothing -> argErr >> exitFailure
> 
>     return (modeflag,notflag,ps)
> 
>   let
>     get xs p = case inv of
>       False -> getEltsByIndex p xs
>       True  -> getEltsByIndex (not . p) xs
> 
>   case mode of
>     Lines -> do
>       lines <- fmap getLines getContents
>       sequence_ $ map putStrLn $ concatMap (get lines) tests
>     ASACC -> do
>       lines <- fmap readCCLines getContents
>       case lines of
>         Nothing -> corrErr >> exitFailure
>         Just zs -> sequence_ $ map (putStrLn . renderCCLine) $ concatMap (get zs) tests
> 
>   exitSuccess
> 
> 
> argErr :: IO ()
> argErr = reportErrorMsgs
>   [ "usage:"
>   , "  getlines INTSET ... : extract lines from stdin at indices in RANGE (sorted)"
>   , "options:"
>   , "  --asacc : read as ASA carriage control lines"
>   ]
> 
> 
> corrErr :: IO ()
> corrErr = reportErrorMsgs
>   [ "corrupt input" ]


Old Stuff
---------

> data CCLine
>   = CCLine [String]
>   deriving (Show)
> 
> 
> renderCCLine :: CCLine -> String
> renderCCLine (CCLine xs)
>   = intercalate "\n" $ zipWith (:) (' ' : (repeat '+')) xs
> 
> 
> unfoldrMaybe :: (b -> Maybe (Maybe (a,b))) -> b -> Maybe [a]
> unfoldrMaybe f x = case f x of
>   Nothing -> Nothing
>   Just Nothing -> Just []
>   Just (Just (a,b)) -> do
>     as <- unfoldrMaybe f b
>     Just (a:as)
> 
> 
> -- write list of messages to stderr
> reportErrorMsgs :: [String] -> IO ()
> reportErrorMsgs errs = do
>   name <- getProgName
>   sequence_ $ map (hPutStrLn stderr) $ ((name ++ " error"):errs)
> 
> 
> -- parse a natural number base 10
> readDecimalNat :: String -> Maybe Int
> readDecimalNat xs = do
>   ys <- sequence $ map decToInt $ reverse xs
>   return $ sum $ zipWith (*) ys [10^t | t <- [0..]]
>   where
>     decToInt :: Char -> Maybe Int
>     decToInt x = lookup x
>       [ ('0',0), ('1',1), ('2',2), ('3',3), ('4',4)
>       , ('5',5), ('6',6), ('7',7), ('8',8), ('9',9)
>       ]
> 
> 
> -- split on \n
> getLines :: String -> [String]
> getLines = unfoldr firstLine
>   where
>     firstLine :: String -> Maybe (String, String)
>     firstLine xs = case break (== '\n') xs of
>       ("","")   -> Nothing
>       (as,"")   -> Just (as,"")
>       (as,b:bs) -> Just (as,bs)
