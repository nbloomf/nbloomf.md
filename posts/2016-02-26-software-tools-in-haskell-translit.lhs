---
title: Software Tools in Haskell: translit
subtitle: transliterate or remove chars on stdin
date: 2016-02-26
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-02-26-software-tools-in-haskell-translit.lhs) into GHCi and play along. As usual, we start with some imports.

> -- sth-translit: transliterate characters on stdin
> module Main where
> 
> import System.Environment (getArgs, getProgName)
> import System.Exit (exitSuccess, exitFailure)
> import System.IO (hPutStrLn, stderr)
> import Data.List (unfoldr)
> import Data.Char (readLitChar)

The purpose of ``translit`` is to replace characters by other characters; it applies a mapping with signature ``Char -> Char`` to each character on stdin. (While simple, this is surprisingly useful.) The most succinct way to specify such a mapping is with two lists of characters, one denoting the domain of the character mapping and the other the codomain. For instance, calling

    translit "abc" "xyzw"

replaces all ``a``s by ``x``, ``b``s by ``y``, and ``c``s by ``z``. (The ``w`` has no effect.) It is useful if we can also specify *ranges* of characters with hyphens. For instance the string ``a-g`` should be shorthand for ``abcdefg``. If the second list is nonempty, but shorter than the first, we pretend its final character is repeated indefinitely, so that

    translit "abc" "x"

replaces all copies of ``a``, ``b``, or ``c`` by ``x``.

If the second list is empty or not given, we can reasonably interpret this to mean we should remove the characters in the first list from the input. This is all well and good.

I have one quibble with Kernighan and Plauger's design, though; they introduce another special input case. If the second list contains 0 or 1 characters, then the first list can be prepended by a "not" symbol like so:

    translit -"abc" "x"

This means to replace every character *except* ``a``, ``b``, and ``c`` by ``x``. I respectfully claim that this is the Wrong Thing. The arguments to ``translit`` are shorthand for a mapping, given in the form of two **lists**. We can tell by the significance of order; ``translit ab xy`` is not the same as ``translit ba xy``. It is only by a quirk of combinatorics that this dependence on order goes away if the second list has 0 or 1 entry. But the special "not" option implicitly treats the arguments of ``translit`` as **sets**. To see this, think about what the complement of a list of characters is. In principle we could say that ``-"a-z"``, as a list, means all characters (in order) except for the lower case roman letters. But is this useful? For instance, what if the user tries to run

    translit -"abc" "xy"

What does this mean? Is the ``y`` just ignored? (User input should not be silently ignored.) Does the first unicode code point get mapped to ``x``, and all others to ``y``? Is this useful? Is it useful enough to warrant complicating ``translit`` with the extra code needed to handle this special case of a special case? I don't think it is.

But the ability to replace or remove characters from a *set complement* is useful. And so I will split ``translit`` into two: ``translit`` will handle the list-wise mapping of characters, and a separate program, ``charreplace``, will handle set-wise mappings. My opinion (and it's just an opinion!) is that these two uses are different enough, semantically, to deserve separate tools; this avoids burdening the user with too many special cases and cluttering the interface with delicate options.

We already have most of the machinery needed for ``translit``, except for the code needed to interpret command line arguments. We introduce an internal representation of character sequences: a character sequence is a list of either single characters or ranges of characters.

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

Now the main program just has to interpret its arguments and call some library functions.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   (from,to) <- case map (readCharSeq . bsUnEsc) args of
>     [Just as]          -> return (as, "")
>     [Just as, Just bs] -> return (as, bs)
>     otherwise          -> argError
> 
>   let
>     remove   = filter (not . (`elem` from))
>     translit = map (applyListMap $ zip from (padLast to))
> 
>   case to of
>     ""        -> charFilter remove
>     otherwise -> charFilter translit
> 
>   exitSuccess
> 
> 
> argError :: IO a
> argError = reportErrorMsgs
>   [ "usage:"
>   , "  translit [FROM] [TO]  -- replace chars in FROM by those in TO"
>   , "  translit [REMOVE]     -- remove chars in REMOVE"
>   ] >> exitFailure
> 
> 
> padLast :: [a] -> [a]
> padLast []     = []
> padLast [x]    = repeat x
> padLast (x:xs) = x : padLast xs

Note that the arguments of ``translit`` are run through ``bsUnEsc``, so that we can easily work with otherwise untypeable characters. (We could, for example, use this to replace ``charfullwidth``.) With ``translit``, many of the small tools we've written so far can suddenly be combined to do neat things. As a simple example, put the following text in a file called ``unicode-test.txt``.

```
\uxyz0 \uxyz1 \uxyz2 \uxyz3
\uxyz4 \uxyz5 \uxyz6 \uxyz7
\uxyz8 \uxyz9 \uxyza \uxyzb
\uxyzc \uxyzd \uxyze \uxyzf
```

Now the pipeline

    cat unicode-test.txt | translit "xyz" "001" | unescape

replaces the ``x``, ``y``, and ``z`` with ``0``, ``0``, and ``1`` and interprets the ``\uXXXX`` as escape codes. This lets us see what several unicode code points look like at one time. With a larger "template" file we could see more characters at a time.


Old Stuff
---------

> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
> 
> 
> -- apply a list of input-output pairs
> applyListMap :: (Eq a) => [(a,a)] -> a -> a
> applyListMap zs x = case lookup x zs of
>   Nothing -> x
>   Just y  -> y
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
