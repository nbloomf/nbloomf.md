---
title: Align
author: nbloomf
date: 2015-07-27
tags: literate-haskell, munge
---

> module Align where
> 
> import Data.List
> import System.IO
> import System.Environment
> import System.Console.GetOpt
> import System.Exit
> 
> align :: [String] -> String -> String
> align [] xs     = xs
> align (d:ds) xs = align ds $ align' d xs
> 
> align' sep str = unlines $ map stripSpaces $ map concat $ baz
>   where
>     foo = map (splitBy' sep) $ lines str
>     bar = maxLengths foo
>     baz = [zipWith (padWith ' ') bar xs | xs <- foo]
> 
>     stripSpaces = reverse . dropWhile (==' ') . reverse
> 
> splitBy :: (Eq a) => [a] -> [a] -> [[a]]
> splitBy sep xs = foo $ filter (isPrefixOf sep . snd) $ zip (inits xs) (tails xs)
>   where
>     foo []        = [xs]
>     foo ((a,b):_) = a : splitBy sep (strip sep b)
> 
>     strip [] bs = bs
>     strip _  [] = []
>     strip (a:as) (b:bs) = if a==b then strip as bs else b:bs
> 
> splitBy' :: (Eq a) => [a] -> [a] -> [[a]]
> splitBy' sep xs = foo $ splitBy sep xs
>   where foo (y:ys) = y : map (sep++) ys
> 
> joinBy :: [a] -> [[a]] -> [a]
> joinBy sep = concat . intersperse sep
> 
> padWith :: a -> Int -> [a] -> [a]
> padWith fill n xs = take n $ xs ++ (repeat fill)
> 
> maxLengths :: [[[a]]] -> [Int]
> maxLengths xsss = map maximum $ transpose $ map (padWith 0 m . map length) xsss
>   where m = maximum $ map length xsss
> 
> 
> main = do
>   args               <- getArgs
>   (actions, _, errs) <- return $ getOpt Permute options args
>   opts               <- foldl (>>=) (return defaultArgs) actions
> 
>   {---------------------------------------------------}
>   {- If any command line errors, show usage and quit -}
>   {---------------------------------------------------}
>   _ <- if errs == []
>         then return ()
>         else showErrors errs >> showUsage >> exitWith (ExitFailure 1)
> 
>   {-----------------------------------------}
>   {- If --help is set, show usage and quit -}
>   {-----------------------------------------}
>   _ <- if (helpFlag opts) == True
>         then showUsage >> exitWith ExitSuccess
>         else return ()
> 
>   f <- if (inputFlag opts == True)
>         then readFile (inputPath opts)
>         else getContents
> 
>   let sep = splitBy (delimiterString opts) (separatorString opts)
> 
>   putStr (align sep f)
>   exitWith ExitSuccess
> 
> showUsage     = hPutStrLn stdout (usageInfo "Usage: a [OPTION...]" options)
> showErrors es = hPutStrLn stderr (concat es)
> 
> data Flag = Flag
>  { inputFlag :: Bool, inputPath :: String
>  , separatorFlag :: Bool, separatorString :: String
>  , delimiterFlag :: Bool, delimiterString :: String
>  , helpFlag :: Bool
>  } deriving (Eq, Show)
> 
> defaultArgs = Flag
>  { inputFlag = False,     inputPath = ""
>  , separatorFlag = False, separatorString = "& \\\\"
>  , delimiterFlag = False, delimiterString = " "
>  , helpFlag = False
>  }
> 
> options :: [OptDescr (Flag -> IO Flag)]
> options = 
>  [ Option [] ["help"]
>      (NoArg (\opt -> return $ opt {helpFlag = True}))
>      "show usage"
> 
>  , Option ['i'] ["input"]
>      (ReqArg (\arg opt -> return $ opt {inputFlag = True, inputPath = arg}) "FILE")
>      "input (if not set, use stdin)"
> 
>  , Option ['s'] ["separators"]
>      (ReqArg (\arg opt -> return $ opt {separatorFlag = True, separatorString = arg}) "STRING")
>      "separators (if not set, use & and \\\\)"
> 
>  , Option ['d'] ["delimiter"]
>      (ReqArg (\arg opt -> return $ opt {delimiterFlag = True, delimiterString = arg}) "STRING")
>      "delimiter (if not set, use space)"
>  ]
