---
title: "Software Tools in Haskell: entab"
subtitle: replace spaces on stdin with tabs
date: 2016-02-18
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-entab: replace spaces on stdin with tabs
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import System.IO (hPutStrLn, stderr)
> import Control.Arrow ((>>>))
> import Data.List (unfoldr)

The [``detab``](/posts/2016-02-15-software-tools-in-haskell-detab.html) program replaced tab characters with spaces, taking arguments at the command line to let the user specify the width of the tab stops. The ``entab`` program reverses this process. It takes input which we assume represents some tabular data where different columns start on specific character columns, chops the input lines into columns, and replaces any trailing spaces in a given column by a single ``\t`` character. Just like ``detab``, the default tab stop width is 8, and we allow the user to specify a list of tab stop widths at the command line with the convention that the *last* user-specified width is assumed to repeat indefinitely.

The basic structure of this program is nearly identical to that of ``detab`` (which is not surprising).

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   -- Read positive integer tabstop arguments.
>   -- Default is [8].
>   ts <- case readPosIntList args of
>     Just [] -> return [8]
>     Just ks -> return ks
>     Nothing -> reportErrorMsgs
>                  ["tab widths must be positive integers."
>                  ] >> exitFailure
> 
>   -- Do it!
>   lineFilter (insertTabStops ts)
>   exitSuccess

We reuse the functions for reading lists of nonnegative integers that we wrote for ``detab``. The heavly lifting is done by ``insertTabStops``.

> insertTabStops :: [Int] -> String -> String
> insertTabStops [] xs = xs
> insertTabStops ks xs = accum [] ks xs
>   where
>     accum zs _ "" = concat $ reverse zs
>     accum zs [t] ys =
>       let (as,bs) = splitColumn t ys in
>       accum (as:zs) [t] bs
>     accum zs (t:ts) ys =
>       let (as,bs) = splitColumn t ys in
>       accum (as:zs) ts bs
> 
>     splitColumn :: Int -> String -> (String, String)
>     splitColumn k xs
>       | k  <= 0   = (xs,"")
>       | xs == ""  = ("","")
>       | otherwise = (ds,bs)
>           where
>             (as,bs) = splitAt k xs
>             munch = dropWhile (== ' ')
>             cs = reverse as
>             ds = if bs == ""
>                      then let es = reverse $ munch cs in
>                        if es == "" then "\t" else es
>                      else case cs of
>                        ' ':_ -> reverse ('\t':(munch cs))
>                        otherwise -> as

Even the shape of this function on the page resembles that of its counterpart from ``detab``. Note the use of an accumulating parameter helper function.

In Exercise 2-2, Kernighan and Plauger ask us to make the simplest change to ``entab`` to make it handle tabs correctly. After thinking about this, I've decided the right thing to do is **nothing**. Let's imagine what it means if the user is trying to use ``entab`` on data that contains tabs. I can think of two possible situations.

1. The tabs are "semantic tabs", used to delimit data. That is, the input either is already tab-delimited, or contains a mixture of tab-delimited and column-delimited data. In this case the user has other problems. The right thing to do in the first case is nothing, and in the second case depends on the user's intent. We could assume that a semantic tab means "advance to the next tab stop", but this now changes the column indices of the characters in the remainder of the line unpredictably, so the intent of any tab stop width input is unclear. It would be better here to run the data through ``detab`` first to remove the tabs, then run through ``entab`` to put them back.
2. The tabs are "literal tabs", as in the data itself involves tab characters for some reason, and they have a different meaning in whatever context the user cares about. This is, after all, a valid reason to use a column-delimited format. Of course in this case the right thing to do is leave the tabs alone.

If we ignore tabs altogether, then at best this is the Right Thing and at worst the user has to use ``detab`` first (or has other problems). On the other hand, trying to make ``entab`` do something useful with tabs would make the program more complicated (and probably clutter the interface) with little benefit.

Old stuff:

> -- parse a list of positive integers base 10
> readPosIntList :: [String] -> Maybe [Int]
> readPosIntList = map readDecimalNat
>   >>> map (filterMaybe (>0))
>   >>> sequence
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
> -- apply a map to all lines on stdin
> lineFilter :: (String -> String) -> IO ()
> lineFilter f = do
>   xs <- fmap getLines getContents
>   sequence_ $ map (putStrLn . f) xs
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
> 
> 
> filterMaybe :: (a -> Bool) -> Maybe a -> Maybe a
> filterMaybe p x = do
>   y <- x
>   case p y of
>     True  -> Just y
>     False -> Nothing
