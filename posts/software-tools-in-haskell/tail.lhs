---
title: "Software Tools in Haskell: tail"
subtitle: get the last k lines or chars from stdin
date: 2016-02-28
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- tail: get the last k lines or chars from stdin
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import System.IO (hPutStrLn, stderr)
> import Data.List (unfoldr)

The version of ``tail`` on my system accepts 10 optional arguments, not including ``--help`` and ``--version``. I am sure that there are very good reasons for these. But this version will take only two: ``--char`` specifies that we want to take the last few characters, rather than lines, and an optional integer argument specifies the number to take.

We use a data type, ``Mode``, to represent the processing mode (lines or chars). Most of the complexity is in reading arguments and reporting errors.

> data Mode = Chars | Lines
> 
> main :: IO ()
> main = do
>   args <- getArgs
> 
>   (mode,k) <- do
>     (flag,rest) <- case args of
>       ("--char":xss) -> return (Chars,xss)
>       xss            -> return (Lines,xss)
> 
>     case rest of
>       []   -> return (flag,10)
>       [xs] -> case readDecimalNat xs of
>                 Nothing -> argErr >> exitFailure
>                 Just t  -> return (flag,t)
>       _    -> argErr >> exitFailure
> 
>   let
>     getTail = reverse . take k . reverse
> 
>   case mode of
>     Chars -> fmap getTail getContents
>                >>= putStr
>     Lines -> fmap (getTail . getLines) getContents
>                >>= (sequence_ . map putStrLn)
> 
>   exitSuccess
> 
> 
> argErr :: IO ()
> argErr = reportErrorMsgs
>   [ "usage:"
>   , "  tail     : send the last 10 lines of stdin to stdout"
>   , "  tail INT : send the last INT lines of stdin to stdout"
>   , "options:"
>   , "  --char : get chars instead of lines"
>   ]


Old Stuff
---------

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
> 
> 
> -- write list of messages to stderr
> reportErrorMsgs :: [String] -> IO ()
> reportErrorMsgs errs = do
>   name <- getProgName
>   sequence_ $ map (hPutStrLn stderr) $ ((name ++ " error"):errs)
