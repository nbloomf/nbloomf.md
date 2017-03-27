---
title: Software Tools in Haskell: charreplace
subtitle: replace chars by strings on stdin
date: 2016-02-27
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-02-27-software-tools-in-haskell-charreplace.lhs) into GHCi and play along. As usual, we start with some imports.

> -- sth-charreplace: replace chars with strings on stdin
> module Main where
> 
> import System.Environment (getArgs, getProgName)
> import System.Exit (exitSuccess, exitFailure)
> import Data.List (unfoldr)
> import Data.Char (readLitChar)
> import System.IO (hPutStrLn, stderr)

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
