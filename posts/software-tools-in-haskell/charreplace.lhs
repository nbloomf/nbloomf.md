---
title: Software Tools in Haskell: charreplace
subtitle: replace chars by strings on stdin
date: 2016-02-27
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-charreplace: replace chars with strings on stdin
> module Main where
> 
> import System.Environment (getArgs, getProgName)
> import System.Exit (exitSuccess, exitFailure)
> import System.IO (hPutStrLn, stderr)

See also the [Backslash](/posts/software-tools-in-haskell/Lib/Backslash.html) module.

> import Lib.Backslash (bsUnEsc)

The program ``charreplace`` is a companion to [``translit``](/pages/sth/tool/translit.html) and requires no new machinery.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   (notflag,from,to) <- do
>     let
>       (flag,rest) = case args of
>         ("--not":xs) -> (True,xs)
>         xs           -> (False,xs)
> 
>     (from,to) <- case rest of
>       [as] -> case readCharSeq (bsUnEsc as) of
>         Just xs -> return (xs, "")
>         Nothing -> argError
>       [as,bs] -> case readCharSeq (bsUnEsc as) of
>         Just xs -> return (xs, bsUnEsc bs)
>         Nothing -> argError
>       otherwise -> argError
> 
>     return (flag,from,to)
> 
>   let
>     remove = case notflag of
>       False -> filter (not . (`elem` from))
>       True  -> filter (`elem` from)
> 
>   let
>     replace = case notflag of
>       False -> concatMap
>                  (\x -> if x`elem`from then to else [x])
>       True  -> concatMap
>                  (\x -> if x`elem`from then [x] else to)
> 
>   case to of
>     ""        -> charFilter remove
>     otherwise -> charFilter replace
> 
>   exitSuccess
> 
> 
> argError :: IO a
> argError = reportErrorMsgs
>   [ "usage:"
>   , "  charreplace [SOURCE] [TARGET] -- replace each char in SOURCE with TARGET string"
>   , "  charreplace [REMOVE]          -- remove each char in REMOVE string"
>   , "option:"
>   , "  --not  : invert selection (e.g. replace all *except* SOURCE)"
>   ] >> exitFailure

It may seem like overkill to split the functionality from ``translit`` and ``charreplace`` just to make the interface more consistent. But note that ``charreplace`` naturally does something we couldn't have done if the two were rolled together, at least not without making the interface even *more* inconsistent: ``charreplace`` naturally replaces characters by **strings**, not just characters. This is not a trivial distinction; for example, if we have a text file which uses unix-style line endings (``\n``) and want to convert them to Windows-style line endings (``\r\n``) we can do this with

    charreplace "\n" "\r\n"

I can't think of a way to do this with ``translit`` alone.


Old Stuff
---------

> data CCLine
>   = CCLine [String]
>   deriving (Show)
> 
> 
> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
> 
> 
> -- write list of messages to stderr
> reportErrorMsgs :: [String] -> IO ()
> reportErrorMsgs errs = do
>   name <- getProgName
>   sequence_ $ map (hPutStrLn stderr) $ ((name ++ " error"):errs)
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
> data CharSeq
>   = Single Char
>   | Range  Char Char
>   deriving (Show)
> 
> readCharSeq :: String -> Maybe String
> readCharSeq = fmap charSeqsToList . readCharSeqs . bsUnEsc
>   where
>     charSeqsToList :: [CharSeq] -> String
>     charSeqsToList = concatMap charSeqToList
>       where
>         charSeqToList (Single x)  = [x]
>         charSeqToList (Range x y) = enumFromTo x y
>     
>     readCharSeqs :: String -> Maybe [CharSeq]
>     readCharSeqs = unfoldrMaybe firstCharSeq
>       where
>         firstCharSeq :: String -> Maybe (Maybe (CharSeq, String))
>         firstCharSeq ""      = Just Nothing
>         firstCharSeq [x]     = Just (Just (Single x, ""))
>         firstCharSeq ('-':_) = Nothing
>         firstCharSeq [x,y]   = Just (Just (Single x, [y]))
>         firstCharSeq (x:y:z:xs) = case y of
>           '-' -> Just (Just (Range x z, xs))
>           otherwise -> Just (Just (Single x, y:z:xs))
