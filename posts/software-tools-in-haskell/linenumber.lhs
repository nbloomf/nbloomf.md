---
title: Software Tools in Haskell: line number
subtitle: number lines on stdin
date: 2016-03-09
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- linenumber: number lines on stdin
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import System.IO (hPutStrLn, stderr)
> import Data.List (unfoldr)

This is another utility intended for use with ``pslineprint``: it prepends lines on ``stdin`` with line numbers.

By default, this program separates the line number from the line contents by a tab; the output is tab-delimited text. This reflects the fact that the line number is semantically distinct from the line contents. The ``--pad`` option instead separates the numbers from the contents by a space, and also left-pads the numbers so that they are vertically aligned and right-justified. Finally, the ``--from`` option allows the user to specify the number of the first line (natural numbers only).

We made tab-separated output the default because it is the simplest; we can march down the list of lines on ``stdin`` and send them to ``stdout`` with the numer prefixed. We only need to keep track of the current line number. Nicely padded line numbers with spaces, however, require us to know in advance the total number of lines required before we can begin producing output.

> data Mode = Tab | Pad
> 
> main :: IO ()
> main = do
>   args <- getArgs
> 
>   (mode,from) <- do
>     let
>       (m,rest) = case args of
>         ("--pad":xs) -> (Pad, xs)
>         xs           -> (Tab, xs)
> 
>     case rest of
>       ["--from",k] -> case readDecimalNat k of
>         Nothing -> argErr >> exitFailure
>         Just t  -> return (m,t)
>       otherwise -> return (m,1)
> 
>   lns <- fmap ((zip [from..]) . getLines) getContents
> 
>   case mode of
>     Tab -> do
>       let wr (a,str) = show a ++ "\t" ++ str
>       sequence_ $ map putStrLn $ map wr lns
> 
>     Pad -> do
>       let
>         len = case lns of
>           [] -> 0
>           zs -> length $ show $ fst $ last zs
>         pad n = padToByBefore len ' ' (show n)
>         wr (a,str) = pad a ++ " " ++ str
>       sequence_ $ map putStrLn $ map wr lns
> 
>   exitSuccess
> 
> 
> 
> argErr :: IO ()
> argErr = reportErrorMsgs
>   [ "usage:"
>   , "  linenumber       : prepend line numbers (tab separated)"
>   , "  linenumber --pad : prepend line numbers (padded with spaces)"
>   , "options:"
>   , "  --from NAT : start numbering at NAT; default is 1"
>   ]

This program uses one new library function: ``padToByBefore``, the companion of ``padToByAfter``.

> padToByBefore :: Int -> a -> [a] -> [a]
> padToByBefore k z xs = reverse $ padToByAfter k z (reverse xs)


Old Stuff
---------

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
> --  'padToByAfter' takes an integer k, a thing
> --  z, and a list xs, and returns a list of length
> --  k consisting of the elements of xs pads xs to length k
> --  by postpending copies of z. If xs is longer
> --  than k there is an error. (We take "pad" very
> --  seriously.)
> padToByAfter :: Int -> a -> [a] -> [a]
> padToByAfter k z xs = take k (xs ++ repeat z)
