---
title: "Software Tools in Haskell: expand"
subtitle: uncompress text on stdin (run length encoding)
author: nbloomf
date: 2016-02-24
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-expand: uncompress stdin (run length encoding)
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.IO (hPutStrLn, stderr)
> import System.Environment (getProgName)

The companion to [``compress``](/posts/2016-02-23-software-tools-in-haskell-compress.html) is ``expand``. It reads a string of characters that was run length encoded by ``compress`` and uncompresses it. This program has an error condition; the input may not be valid. This can happen for a few reasons; if a repeat count is incorrectly encoded (i.e. includes invalid digits or does not terminate in a sigil), or if the file ends in the middle of a repeat encoding.

> main :: IO ()
> main = do
>   xs <- getContents
> 
>   ys <- case rlDecode '\BEL' xs of
>           Just zs -> return zs
>           Nothing -> reportErrorMsgs
>                        [ "corrupt input"
>                        ] >> exitFailure
> 
>   putStr ys
>   exitSuccess

``rlDecode`` does all the work:

> rlDecode :: Char -> String -> Maybe String
> rlDecode sig = fmap (runLengthDecode sig) . readRLE sig
>   where
>     runLengthDecode :: (Eq a) => a -> [RLE a] -> [a]
>     runLengthDecode sig = concatMap decodeRLE
>       where
>         decodeRLE (Chunk  xs)  = xs
>         decodeRLE (Repeat k x) = replicate k x
>         decodeRLE (Literal k)  = replicate k sig
> 
>     readRLE :: Char -> String -> Maybe [RLE Char]
>     readRLE sig = unfoldrMaybe readFirstRLE
>       where
>         readFirstRLE :: String -> Maybe (Maybe (RLE Char, String))
>         readFirstRLE ""  = Just Nothing
>         readFirstRLE [x] =
>           if x == sig then Nothing else Just (Just (Chunk [x], ""))
>         readFirstRLE [x,y] =
>           if x == sig then Nothing else Just (Just (Chunk [x], [y]))
>         readFirstRLE (x:y:z:xs)
>           | x == sig && y == sig && z == sig
>               = Just (Just (Literal 1, xs))
>           | x == sig && y == sig && z /= sig
>               = do
>                   let (as,bs) = span (/= sig) (z:xs)
>                   k <- readBase86Nat as
>                   case bs of
>                     ""     -> Just (Just (Repeat k y, ""))
>                     (_:cs) -> Just (Just (Repeat k y, cs))
>           | x == sig && y /= sig
>               = do
>                   let (as,bs) = span (/= sig) (z:xs)
>                   k <- readBase86Nat as
>                   case bs of
>                     ""     -> Just (Just (Repeat k y, ""))
>                     (_:cs) -> Just (Just (Repeat k y, cs))
>           | otherwise
>               = do
>                   let (as,bs) = span (/= sig) (x:y:z:xs)
>                   Just (Just (Chunk as, bs))

``readBase86Nat`` is the companion to ``showBase86Nat``:

> readBase86Nat :: String -> Maybe Int
> readBase86Nat xs = do
>   ys <- sequence $ map charToInt $ reverse xs
>   return $ sum $ zipWith (*) ys [86^t | t <- [0..]]
>   where
>     charToInt :: Char -> Maybe Int
>     charToInt x = lookup x
>       [ ('0',0),  ('1',1),  ('2',2),  ('3',3),  ('4',4)
>       , ('5',5),  ('6',6),  ('7',7),  ('8',8),  ('9',9)
>       , ('a',10), ('b',11), ('c',12), ('d',13), ('e',14)
>       , ('f',15), ('g',16), ('h',17), ('i',18), ('j',19)
>       , ('k',20), ('l',21), ('m',22), ('n',23), ('o',24)
>       , ('p',25), ('q',26), ('r',27), ('s',28), ('t',29)
>       , ('u',30), ('v',31), ('w',32), ('x',33), ('y',34)
>       , ('z',35), ('A',36), ('B',37), ('C',38), ('D',39)
>       , ('E',40), ('F',41), ('G',42), ('H',43), ('I',44)
>       , ('J',45), ('K',46), ('L',47), ('M',48), ('N',49)
>       , ('O',50), ('P',51), ('Q',52), ('R',53), ('S',54)
>       , ('T',55), ('U',56), ('V',57), ('W',58), ('X',59)
>       , ('Y',60), ('Z',61), ('?',62), ('!',63), ('#',64)
>       , ('&',65), ('@',66), ('$',67), ('=',68), ('+',69)
>       , ('-',70), ('~',71), ('<',72), ('>',73), ('[',74)
>       , (']',75), ('(',76), (')',77), ('{',78), ('}',79)
>       , ('|',80), ('/',81), ('*',82), ('^',83), (':',84)
>       , (';',85)
>       ]

One big improvement we could make to ``expand`` is to try to handle invalid input more gracefully; we could output the partially expanded text, for instance, or tell the user exactly where the error occurs. The first idea would not be too difficult. (Write the output to stderr.) The second idea, though, while possibly useful, would make the implementation much more complicated. (We'd have to keep track of the position of each character in the original source.) Doable, but until the need is demonstrated I'd prefer to keep the implementation simple.

Old stuff:

> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
> 
> 
> -- run length encoding
> data RLE a
>   = Chunk   [a]
>   | Repeat  Int a
>   | Literal Int
>   deriving Show
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
> digitsToBase :: (Integral n) => n -> n -> [n]
> digitsToBase b k
>   | b <= 1 || k <= 0 = []
>   | otherwise = reverse $ foo k
>       where
>         foo t
>           | t < b = [t]
>           | otherwise = (t`rem`b) : (foo (t`quot`b))
> 
> 
> -- write list of messages to stderr
> reportErrorMsgs :: [String] -> IO ()
> reportErrorMsgs errs = do
>   name <- getProgName
>   sequence_ $ map (hPutStrLn stderr) $ ((name ++ " error"):errs)
