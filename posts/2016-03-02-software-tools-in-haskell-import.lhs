---
title: Software Tools in Haskell: import
subtitle: splice contents of a file into stdin
date: 2016-03-02
author: nbloomf
tags: software-tools-in-haskell
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2016-03-02-software-tools-in-haskell-import.lhs) into GHCi and play along. As usual, we start with some imports.

> -- import: splice contents of a file into stdin
> module Main where
> 
> import System.Exit (exitSuccess, exitFailure)
> import System.Environment (getArgs, getProgName)
> import Data.List (unfoldr)
> import Data.Char (isSpace)
> import System.IO (hPutStrLn, stderr)

The ``import`` tool takes lines one at a time, writing them back to ``stdout`` until it sees one of the form

    import FILENAME

These lines should instead be replaced by the contents of ``FILENAME`` (relative to the working directory). I will make two tweaks: first, this program implicitly imposes a format on its input. To avoid being too opinionated, I will make the import "keyword" a parameter, so that if the user runs

    import --with "go-go-gadget"

then the program will instead look for lines of the form

    go-go-gadget FILENAME

This is because the text being filtered may have some other implicit format, where the word "import" means something. The second tweak is to allow the user to import only part of a file. If an import command has the form

    import FILENAME between OPEN and CLOSE

then only those lines from FILENAME which are between lines OPEN and CLOSE are spliced in.

First, we write a generic function called ``takeBetween`` which cuts out portions of a list.

> takeBetween :: (Eq a) => (a,a) -> [a] -> [a]
> takeBetween (u,v) = concat . unfoldr (firstCut (u,v))
>   where
>     firstCut (u,v) ys = case dropWhile (/= u) ys of
>       []     -> Nothing
>       (_:zs) -> Just $ span (/= v) zs

We use a custom data type, ``Import``, to represent the two kinds of import commands. The ``readCommand`` function tries to interpret a line of text as an import command, and the ``splice`` function processes a single line of text (from reading a command to splicing in text from an external file). Now the main program behaves very much like a line filter, which we recall takes a mapping ``String -> String`` and applies it to all lines on ``stdin``. Because ``splice`` reads files and writes to ``stdout``, it must take place in the ``IO`` monad; its signature is ``String -> IO ()``. We write a variant of ``lineFilter`` to handle programs of this type.

> lineFilterIO :: (String -> IO ()) -> IO ()
> lineFilterIO f = do
>   xs <- fmap getLines getContents
>   sequence_ $ map f xs

The program is then not terribly complicated:

> -- We accept two kinds of import commands:
> data Import
>   = Whole   String
>   | Between String String String
> 
> 
> main :: IO ()
> main = do
>   args <- getArgs
> 
>   keyword <- case args of
>     []             -> return "import"
>     ["--with",str] -> return str
>     otherwise      -> argErr >> exitFailure
> 
>   let
>     -- see if a line is an import command
>     readCommand :: String -> Maybe Import
>     readCommand str = case getWords str of
>       [x,file] -> if x == keyword
>         then Just $ Whole file
>         else Nothing
>       [x,file,"between",open,"and",close] -> if x == keyword
>         then Just $ Between file open close
>         else Nothing
>       otherwise -> Nothing
> 
>     -- process a single line
>     splice :: String -> IO ()
>     splice line = case readCommand line of
>       Nothing -> do
>         putStrLn line
>       Just (Whole name) -> do
>         input <- fmap getLines $ readFile name
>         sequence_ $ map putStrLn input
>       Just (Between name open close) -> do
>         input <- fmap getLines $ readFile name
>         sequence_ $ map putStrLn $ takeBetween (open,close) input
> 
>   lineFilterIO splice
>   exitSuccess
> 
> 
> argErr :: IO ()
> argErr = reportErrorMsgs
>   [ "usage"
>   , "  import            : expand any 'import' lines on stdin"
>   , "  import --with STR : same, using custom import keyword STR"
>   , "this program recognizes two kinds of import commands:"
>   , "  import FILENAME"
>   , "    insert contents of FILENAME in place of this line"
>   , "  import FILENAME from START to END"
>   , "    same, but cut out all lines except those between START and END lines."
>   ]

``import`` is used to help produce this documentation. These pages contain lots of code snippets, which are taken from the actual program source code using import commands. This way we don't have to worry about keeping (at least part of) the documentation and the code in sync by hand as the code changes (as it does, frequently).

This tool could be improved in a few ways. First, the import command, filename, and open and close lines must not include any spaces. This may prove to be too restrictive; we could allow for quoted arguments or escaped arguments. Second, we could do something a litte more informative when ``readFile`` fails because a file does not exist; this version of ``import`` knows nothing about where a given import command came from. In a large pipeline, or a small pipeline operating on lots of data, this may be a problem.


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
> -- split a string into words
> getWords :: String -> [String]
> getWords = unfoldr firstWord
>   where
>     firstWord :: String -> Maybe (String, String)
>     firstWord xs = case dropWhile isSpace xs of
>       "" -> Nothing
>       ys -> Just $ break isSpace ys
