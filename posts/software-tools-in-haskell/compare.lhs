---
title: Software Tools in Haskell: compare
subtitle: find the first position where two text streams differ
date: 2016-03-01
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- compare: find the first position where two text streams differ
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import System.IO (hPutStrLn, stderr)
> import Data.Maybe (maybeToList)
> import Data.List (unfoldr)
> import Data.Char (readLitChar)

The purpose of ``compare`` is to detect whether or not two streams of text are byte-for-byte identical. This alone is simple enough, but the job is complicated by the fact that (1) there are a few useful places these text streams might come from and (2) in the (typical) case that the streams are *not* identical, we want to report the position of the first difference.

The ``diffList`` function takes two lists and returns the position of the earliest difference as well as the differing elements (if they exist).

> diffList :: (Eq a) => [a] -> [a] -> (Maybe a, Maybe a, Integer)
> diffList = comp 1
>   where
>     comp _ []     []     = (Nothing, Nothing, 0)
>     comp k []     (y:_)  = (Nothing, Just y, k)
>     comp k (x:_)  []     = (Just x, Nothing, k)
>     comp k (x:xs) (y:ys) = if x == y
>       then comp (k+1) xs ys
>       else (Just x, Just y, k)

This isn't quite what we want, though. The problem is that word "position". The most useful *position* information will depend on what kind of text is being compared. For instance, when comparing line text we'd like to report the line and column numbers of the earliest difference, rather than just the character index. The ``diffLists`` function does this.

> diffLists :: (Eq a) => [[a]] -> [[a]]
>   -> (Maybe [a], Maybe [a], Integer, Integer)
> diffLists = comp 1
>   where
>     comp _ []       []       = (Nothing, Nothing, 0, 0)
>     comp m []       (ys:yss) = (Nothing, Just ys, m, 1)
>     comp m (xs:xss) []       = (Just xs, Nothing, m, 1)
>     comp m (xs:xss) (ys:yss) = case diffList xs ys of
>       (Nothing, Nothing, _) -> comp (m+1) xss yss
>       (_,_,n) -> (Just xs, Just ys, m, n)

Like we did with ``echo``, we'll allow the user to specify which kind of position they mean with a ``--char`` option (default is line). Now the streams to be compared (of which we need two) can come from one of three places:

1. ``stdin``,
2. a file (one or two), or
3. command line arguments (interpreted like ``echo``).

The main program first reads the arguments and extracts (1) the mode (char or line) of text being compared, (2) the name and contents of the first stream to be compared, and (3) the name and contents of the second stream to be compared. Then we evaluate either ``diffList`` or ``diffLists`` and report the results.

> data Mode = Chars | Lines
> 
> main :: IO ()
> main = do
>   args <- getArgs
> 
>   -- interpret arguments
>   (mode,(name1,stream1),(name2,stream2)) <- do
>     let
>       (flag,rest) = case args of
>         ("--char":xss) -> (Chars,xss)
>         xss            -> (Lines,xss)
> 
>     case rest of
>       ("--to":ys) -> do
>         let
>           as = bsUnEsc $ case flag of
>             Chars -> concat ys
>             Lines -> fromLines ys
>         bs <- getContents
>         return (flag,("args",as),("stdin",bs))
>       [xs] -> do
>         as <- readFile xs
>         bs <- getContents
>         return (flag,(xs,as),("stdin",bs))
>       [xs,ys] -> do
>         as <- readFile xs
>         bs <- readFile ys
>         return (flag,(xs,as),(ys,bs))
>       otherwise -> argError >> exitFailure
> 
> 
>   -- Some helpers
>   let
>     (label1,label2) = padToLongerWith ' ' name1 name2
> 
>     report label [] = putStrLn $ label ++ ": (empty)"
>     report label xs = putStrLn $ label ++ ": " ++ xs
> 
> 
>   case mode of
>     Chars -> case diffList stream1 stream2 of
>       (Nothing, Nothing, _) -> return ()
>       (x, y, t) -> do
>         putStrLn $ "first differ at column " ++ show t
>         report label1 (maybeToList x)
>         report label2 (maybeToList y)
> 
>     Lines -> case diffLists (getLines stream1) (getLines stream2) of
>       (Nothing, Nothing, _, _) -> return ()
>       (x, y, m, n) -> do
>         putStrLn $ "first differ at line " ++ show m ++ ", column " ++ show n
>         report label1 (concat $ maybeToList x)
>         report label2 (concat $ maybeToList y) 
> 
>   exitSuccess
> 
> 
> argError :: IO ()
> argError = do
>   reportErrorMsgs
>     [ "usage:"
>     , "  compare FILE1 FILE2  -- find first discrepancy between FILE1 and FILE2"
>     , "  compare FILE         -- find first discrepancy between FILE and stdin"
>     , "  compare --to STR ... -- find first discrepancy between STRs and stdin"
>     , "options:"
>     , "  --char : compare as (unlined) character streams"
>     ]
> 
> 
> padToLongerWith :: a -> [a] -> [a] -> ([a], [a])
> padToLongerWith _ [] [] = ([],[])
> padToLongerWith z [] ys = unzip $ zip (repeat z) ys
> padToLongerWith z xs [] = unzip $ zip xs (repeat z)
> padToLongerWith z (x:xs) (y:ys) =
>   let (as,bs) = padToLongerWith z xs ys
>   in (x:as, y:bs)
> 
> 
> fromLines :: [String] -> String
> fromLines xs = concat $ zipWith (++) xs (repeat "\n")

``compare`` can be used to implement a very simple testing scheme by comparing the output of some program under development to its "expected" output. One improvement I can think of is to have ``compare`` optionally output delimited data, to make it easier to extract this information with other tools.


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
> -- expand C and ASCII style escape codes
> bsUnEsc :: String -> String
> bsUnEsc = concat . unfoldr firstChar
>   where
>     firstChar :: String -> Maybe (String, String)
>     firstChar "" = Nothing
>     firstChar (c:cs) = case c of
>       '\\' -> case cs of
>         -- Basic C-style escape characters
>         ('a' :ds) -> Just ("\a\&",ds)
>         ('b' :ds) -> Just ("\b\&",ds)
>         ('f' :ds) -> Just ("\f\&",ds)
>         ('n' :ds) -> Just ("\n\&",ds)
>         ('r' :ds) -> Just ("\r\&",ds)
>         ('t' :ds) -> Just ("\t\&",ds)
>         ('v' :ds) -> Just ("\v\&",ds)
>         ('\\':ds) -> Just ("\\\&",ds)
>         ('\'':ds) -> Just ("'\&" ,ds)
>         ('"' :ds) -> Just ("\"\&",ds)
>         ('?' :ds) -> Just ("?\&" ,ds)
> 
>         -- 3-digit octal ASCII codes
>         ('0':k2:k3:ds) -> octalCode ['0',k2,k3] ds
>         ('1':k2:k3:ds) -> octalCode ['1',k2,k3] ds
>         ('2':k2:k3:ds) -> octalCode ['2',k2,k3] ds
>         ('3':k2:k3:ds) -> octalCode ['3',k2,k3] ds
>         ('4':k2:k3:ds) -> octalCode ['4',k2,k3] ds
>         ('5':k2:k3:ds) -> octalCode ['5',k2,k3] ds
>         ('6':k2:k3:ds) -> octalCode ['6',k2,k3] ds
>         ('7':k2:k3:ds) -> octalCode ['7',k2,k3] ds
> 
>         -- 2-digit hex ASCII codes
>         ('x':k1:k2:ds) -> case all isHexDigit digs of
>           True  -> case readLitChar ("\\x" ++ digs) of
>             []        -> Just ("\\x" ++ digs, ds)
>             ((x,_):_) -> Just ([x],ds)
>           False -> Just ("\\x" ++ digs, ds)
>           where
>             digs = [k1,k2]
> 
>         -- Standard ASCII abbreviations
>         ('N':'U':'L':ds) -> Just ("\NUL\&", ds)
>         ('S':'O':'H':ds) -> Just ("\SOH\&", ds)
>         ('S':'T':'X':ds) -> Just ("\STX\&", ds)
>         ('E':'T':'X':ds) -> Just ("\ETX\&", ds)
>         ('E':'O':'T':ds) -> Just ("\EOT\&", ds)
>         ('E':'N':'Q':ds) -> Just ("\ENQ\&", ds)
>         ('A':'C':'K':ds) -> Just ("\ACK\&", ds)
>         ('B':'E':'L':ds) -> Just ("\BEL\&", ds)
>         ('D':'L':'E':ds) -> Just ("\DLE\&", ds)
>         ('D':'C':'1':ds) -> Just ("\DC1\&", ds)
>         ('D':'C':'2':ds) -> Just ("\DC2\&", ds)
>         ('D':'C':'3':ds) -> Just ("\DC3\&", ds)
>         ('D':'C':'4':ds) -> Just ("\DC4\&", ds)
>         ('N':'A':'K':ds) -> Just ("\NAK\&", ds)
>         ('S':'Y':'N':ds) -> Just ("\SYN\&", ds)
>         ('E':'T':'B':ds) -> Just ("\ETB\&", ds)
>         ('C':'A':'N':ds) -> Just ("\CAN\&", ds)
>         ('S':'U':'B':ds) -> Just ("\SUB\&", ds)
>         ('E':'S':'C':ds) -> Just ("\ESC\&", ds)
>         ('D':'E':'L':ds) -> Just ("\DEL\&", ds)
>         ('E':'M'    :ds) -> Just ("\EM\&",  ds)
>         ('F':'S'    :ds) -> Just ("\FS\&",  ds)
>         ('G':'S'    :ds) -> Just ("\GS\&",  ds)
>         ('R':'S'    :ds) -> Just ("\RS\&",  ds)
>         ('U':'S'    :ds) -> Just ("\US\&",  ds)
>         ('S':'P'    :ds) -> Just ("\SP\&",  ds)
>         ('B':'S'    :ds) -> Just ("\BS\&",  ds)
>         ('H':'T'    :ds) -> Just ("\HT\&",  ds)
>         ('L':'F'    :ds) -> Just ("\LF\&",  ds)
>         ('V':'T'    :ds) -> Just ("\VT\&",  ds)
>         ('F':'F'    :ds) -> Just ("\FF\&",  ds)
>         ('C':'R'    :ds) -> Just ("\CR\&",  ds)
>         ('S':'O'    :ds) -> Just ("\SO\&",  ds)
>         ('S':'I'    :ds) -> Just ("\SI\&",  ds)
> 
>         -- C99-style universal character names
>         ('u':k1:k2:k3:k4:ds) -> case all isHexDigit digs of
>           True  -> case readLitChar ("\\x" ++ digs) of
>             []        -> Just ("\\u" ++ digs, ds)
>             ((x,_):_) -> Just ([x],ds)
>           False -> Just ("\\u" ++ digs, ds)
>           where
>             digs = [k1,k2,k3,k4]
> 
>         ('U':k1:k2:k3:k4:k5:k6:k7:k8:ds) -> case all isHexDigit digs of
>           True  -> case readLitChar ("\\x" ++ digs) of
>             []        -> Just ("\\U" ++ digs, ds)
>             ((x,_):_) -> Just ([x],ds)
>           False -> Just ("\\U" ++ digs, ds)
>           where
>             digs = [k1,k2,k3,k4,k5,k6,k7,k8]
> 
>         -- stolen from haskell
>         ('&':ds) -> Just ("",ds)
> 
>         -- If we don't see a valid esc code, just move on.
>         ds -> Just ("\\\&", ds)
> 
>       -- No backslash
>       otherwise -> Just ([c],cs)
>       where
>         isHexDigit :: Char -> Bool
>         isHexDigit = (`elem` "0123456789aAbBcCdDeEfF")
> 
>         isOctDigit :: Char -> Bool
>         isOctDigit = (`elem` "01234567")
> 
>         octalCode digs ds = case all isOctDigit digs of
>           True  -> case readLitChar ("\\o" ++ digs) of
>             []        -> Just ('\\':digs, ds)
>             ((x,_):_) -> Just ([x],ds)
>           False -> Just ('\\':digs, ds)
