---
title: "Software Tools in Haskell: paginate"
subtitle: format lines with page numbers and headers
date: 2016-03-06
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ConstrainedClassMethods #-}
> -- paginate: format lines with page numbers and headers
> module Main where
> 
> import System.Console.GetOpt
> import System.Environment (getArgs, getProgName)
> import System.Exit (exitSuccess, exitFailure)
> import System.IO (hPutStrLn, stderr)
> import Data.List (unfoldr, inits, isPrefixOf, intercalate)
> import Data.Foldable (foldl')

Our virtual line printer [``pslineprint``](/posts/2016-03-05-software-tools-in-haskell-pslineprint.html) is nice enough, but extremely simple; it does nothing at all to prettify the documents it prints. Our first attempt at this is ``paginate``. This program will split a sequence of lines into "pages", giving each page a header and page number. It will also be able to print more than one file sequentially, making each file start on its own page and ensuring that page numbers are correct across files. If any file name happens to be ``-``, we read lines from ``stdin``. Finally, it will optionally print a table of contents page in case we are printing a large number of long files.

I think this is the ugliest tool in our kit so far, and that part of the reason for this is that ``paginate`` depends on several arbitrary choices; frequently if there is a single "natural" or "obvious" choice, the resulting code is simple, but if we are making an arbitrary choice among several options our code feels complicated.

First lets look at the main program. Like ``pslineprint``, there are enough options to make it worth our while to use ``GetOpt`` to process them. For now lets suppose we have functions ``paginateLines`` and ``tableOfContents`` that handle all the heavy lifting; the main program logic is mostly straightforward.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   let
>     argErr  = reportErrorMsgs [usageInfo "options" options]
>     corrErr = reportErrorMsgs ["corrupt asacc input"]
> 
> 
>   -- read options
>   (flags, filenames) <- case getOpt Permute options args of
>     (opts, rest, []) -> case foldl (>>=) (Just defaultFlags) opts of
>       Nothing -> argErr >> exitFailure
>       Just fs -> return (fs, rest)
>     otherwise -> argErr >> exitFailure
> 
> 
>   -- process options
>   let
>     pageOpts = PO
>       { linesPerPage = fLinesPerPage flags
>       , lineLength   = fLineLength flags
>       }
> 
> 
>   -- paginate files
>   case fMode flags of
>     Lines -> do
>       let
>         readLines name = case name of
>           "-" -> do
>             lns <- fmap getLines getContents
>             return ("-", lns)
>           otherwise -> do
>             lns <- fmap getLines $ readFile name
>             return (name, lns)
> 
>       docs <- sequence $ map readLines filenames
> 
>       if fPrintTOC flags == False
>         then return ()
>         else sequence_ $ map putStrLn $ tableOfContents pageOpts docs
> 
>       sequence_ $ map putStrLn $ paginateLines pageOpts docs
> 
>     ASACC -> do
>       let
>         readLines name = case name of
>           "-" -> do
>             lns <- fmap readCCLines getContents
>             case lns of
>               Nothing -> corrErr >> exitFailure
>               Just xs -> return ("-", xs)
>           otherwise -> do
>             lns <- fmap readCCLines $ readFile name
>             case lns of
>               Nothing -> corrErr >> exitFailure
>               Just xs -> return (name, xs)
> 
>       docs <- sequence $ map readLines filenames
> 
>       if fPrintTOC flags == False
>         then return ()
>         else sequence_ $ map putStrLn $ map renderCCLine $ tableOfContents pageOpts docs
> 
>       sequence_ $ map putStrLn $ map renderCCLine $ paginateCCLines pageOpts docs
> 
> 
>   exitSuccess
> 
> 
> 
> data Mode = Lines | ASACC
> 
> data Flags = Flags
>   { fLinesPerPage :: Int
>   , fLineLength   :: Int
>   , fPrintTOC     :: Bool
>   , fMode         :: Mode
>   }
> 
> defaultFlags :: Flags
> defaultFlags = Flags
>   { fLinesPerPage = 52
>   , fLineLength   = 75
>   , fPrintTOC     = False
>   , fMode         = Lines
>   }
> 
> 
> options :: [OptDescr (Flags -> Maybe Flags)]
> options =
>   [ Option [] ["lines-per-page"]
>       (ReqArg readLinesPerPage "INT")
>       "number of lines per page (including header)"
> 
>   , Option [] ["line-length"]
>       (ReqArg readLineLength "INT")
>       "length of header lines"
> 
>   , Option [] ["toc"]
>       (NoArg (\opts -> Just $ opts { fPrintTOC = True }))
>       "print table of contents page"
> 
>   , Option [] ["asacc"]
>       (NoArg (\opts -> Just $ opts { fMode = ASACC }))
>       "interpret basic ASA carriage control codes"
>   ]
>   where
>     readLinesPerPage str opts = do
>       k <- readDecimalNat str
>       return $ opts { fLinesPerPage = k }
> 
>     readLineLength str opts = do
>       k <- readDecimalNat str
>       return $ opts { fLineLength = k }

Now for the actual pagination. Generally speaking, ``paginate`` takes a list of lines and inserts new lines -- the headers -- as well as some blank lines in appropriate places, so that the lines can then be taken in chunks of $n$ at a time (called "pages"). But exactly what a "line" is is already ambiguous; of course the usual "text separated by newlines" consists of lines, but so also does a file formatted using ASA carriage control codes. Both kinds of "line" are handled properly by ``pslineprint``, and we already have at least one program, ``overstrike``, which produces carriage control formatted text. So it seems worth our while to make ``paginate`` handle carriage controls as well.

An initial version of this program handled both kinds of line separately, which led to lots of duplicated code. To avoid this, we introduce an abstract ``Line`` type class.

> class Line t where
>   fromString :: String -> t
> 
>   blankLine :: t
>   blankLine = fromString ""
> 
> instance Line String where
>   fromString x = x
> 
> instance Line CCLine where
>   fromString x = CCLine [x]

Also, there are a few tweakable parameters we'd like to be able to adjust: the number of "lines" to appear on each page, and the width (in characters) of the header lines. We wrap these into a type, ``PaginateOpts``, that can be more easily (and meaningfully) be passed around.

> data PaginateOpts = PO
>   { linesPerPage :: Int
>   , lineLength   :: Int
>   } deriving (Show)
> 
> 
> pageCount :: (Line t) => PaginateOpts -> [t] -> Int
> pageCount opts xs = if r == 0 then q else q+1
>   where
>     slpp = (linesPerPage opts) - 2
>     (q,r) = ((count xs) `div` slpp, (count xs) `rem` slpp)
> 
> startPages :: (Line t) => PaginateOpts -> [[t]] -> [Int]
> startPages opts lnss
>   = map (\ks -> 1 + sum ks)
>       $ inits
>       $ map (pageCount opts) lnss
> 
> totalPages :: (Line t) => PaginateOpts -> [[t]] -> Int
> totalPages opts lnss = sum $ map (pageCount opts) lnss

Note that from a ``PaginateOpts`` and a list of (abstract) documents we can compute the total number of pages used and the starting page numbers of each document. These will be used later.

Next we define an abstract page header. Our headers will include three pieces of information: the name of the file being paginated, the current page number, and the total number of pages. We also need a way to convert an abstract header to a list of lines; this is done with ``renderHeader``. We define this function as part of a type class so that we can have different implementations for each kind of line.

> data Header = Header
>   { title      :: String
>   , pageNumber :: Int
>   , pageTotal  :: Int
>   } deriving (Show)
> 
> 
> class RenderHeader t where
>   renderHeader :: (Line t) => PaginateOpts -> Header -> [t]
> 
> 
> instance RenderHeader String where
>   renderHeader opts h = [fn ++ (replicate (ll - nfn - npg) ' ') ++ pg, ""]
>     where
>       pg  = show (pageNumber h) ++ "/" ++ show (pageTotal h)
>       npg = count pg
>       ll  = lineLength opts
>       fn  = if (count $ title h) + npg + 1 > ll
>         then abbr
>         else title h
>       abbr = "..." ++ (reverse $ take (ll - npg - 4) $ reverse $ title h)
>       nfn = count fn
> 
> instance RenderHeader CCLine where
>   renderHeader opts h = map (\x -> CCLine [x]) $ renderHeader opts h

The actual pagination is handled by a few different functions:

* ``splitPages`` divides a document into abstract pages, without proper page numbers.
* ``numberPagesFromOf`` fixes the page numbers of a list of abstract pages, with parameters allowing us to specify where to begin counting from and the total number of pages.
* ``renderPage`` converts an abstract page to a list of lines.
* ``paginateOfFrom`` combines ``splitPages``, ``numberPagesOfFrom``, and ``renderPage`` to paginate a single document.
* ``paginateDocs`` paginates a list of named documents.

> splitPages :: (Line t) => PaginateOpts -> String -> [t] -> [(Header, [t])]
> splitPages opts name = unfoldr firstPage
>   where
>     slpp = (linesPerPage opts) - 2
> 
>     firstPage :: [a] -> Maybe ((Header,[a]),[a])
>     firstPage [] = Nothing
>     firstPage ys = do
>       let
>         (zs,rest) = splitAt slpp ys
>         hdr = Header
>           { title      = name
>           , pageNumber = 0
>           , pageTotal  = 0
>           }
>       return ((hdr, zs), rest)
> 
> 
> numberPagesFromOf :: (Line t)
>   => Int -> Int -> [(Header, [t])] -> [(Header, [t])]
> numberPagesFromOf m n xs = zipWith fix xs [m..]
>   where
>     fix (h,y) k = (h {pageNumber = k, pageTotal = n}, y)
> 
> 
> renderPage :: (Line t, RenderHeader t)
>   => PaginateOpts -> (Header, [t]) -> [t]
> renderPage opts (hdr,lns)
>   = take k ((renderHeader opts hdr) ++ lns ++ repeat blankLine)
>   where k = linesPerPage opts
> 
> 
> paginateOfFrom :: (Line t, RenderHeader t)
>   => PaginateOpts -> Int -> Int -> (String, [t]) -> [t]
> paginateOfFrom opts n m (name, lns)
>   = concatMap (renderPage opts)
>       $ numberPagesFromOf m n
>       $ splitPages opts name lns
> 
> 
> paginateDocs :: (Line t, RenderHeader t)
>   => PaginateOpts -> [(String, [t])] -> [t]
> paginateDocs opts docs
>   = concat $ zipWith (paginateOfFrom opts tot) starts docs
>   where
>     starts = startPages opts $ map snd docs
>     tot    = totalPages opts $ map snd docs

The actual functions we expose from this module are ``paginateLines`` and ``paginateCCLines``, which are just monomorphic synonyms of ``paginateDocs`` for ordinary lines and carriage control formatted lines, and the constructor for ``PaginateOpts``. As far as consumers of this module are concerned, these two black-boxes are implemented separately. Since (as of this writing) the ``Line`` class has only two instances there is no reason to expose the guts of pagination. But by writing our code against an abstract ``Line`` class, it will be easier to extend in the future if needed.

> paginateLines :: PaginateOpts -> [(String, [String])] -> [String]
> paginateLines = paginateDocs
> 
> paginateCCLines :: PaginateOpts -> [(String, [CCLine])] -> [CCLine]
> paginateCCLines = paginateDocs

All that remains is to provide a function for building the table of contents. This part is kind of gross.

> tableOfContents :: (Line t, RenderHeader t)
>   => PaginateOpts -> [(String, [t])] -> [t]
> tableOfContents opts docs = concat $ pad $
>   (fromString "Contents") : blankLine : tocLines
>   where
>     ks = startPages opts $ map snd docs
> 
>     tocLines = zipWith tocLine (map fst docs) ks
> 
>     tocLine name pg = fromString $ padNum pg ++ " " ++ abbr name
> 
>     ll  = lineLength opts
>     abbr str = if (count str) + 5 > ll
>       then "..." ++ (reverse $ take (ll - 9) $ reverse $ str)
>       else str 
> 
>     padNum k = reverse $ take 5 $ (reverse $ show k) ++ repeat ' '
> 
>     pad = unfoldr padFirst
> 
>     padFirst [] = Nothing
>     padFirst xs = Just (take (linesPerPage opts) (ys ++ repeat blankLine), rest)
>       where (ys, rest) = splitAt (linesPerPage opts) xs

A few comments about the default options. I expect that the main use of ``paginate`` will be to prepare documents for ``pslineprint``, and the default settings of that program produce pages with 52 lines per page and about 75 characters per line. Using these as the defaults for ``paginate`` means we can say things like

    paginate foo.txt | pslineprint

and get reasonable results.


Old Stuff
---------

> count :: (Num t) => [a] -> t
> count = foldl' inc 0
>   where inc n _ = n+1
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
> data CCLine
>   = CCLine [String]
>   deriving (Show)
> 
> fromCCLine :: CCLine -> [String]
> fromCCLine (CCLine xs) = xs
> 
> 
> renderCCLine :: CCLine -> String
> renderCCLine (CCLine xs)
>   = intercalate "\n" $ zipWith (:) (' ' : (repeat '+')) xs
>
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
