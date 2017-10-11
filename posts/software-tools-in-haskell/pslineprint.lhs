---
title: Software Tools in Haskell: pslineprint
subtitle: print lines to postscript
date: 2016-03-05
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- pslineprint: print stdin to postscript
> module Main where
> 
> import System.Console.GetOpt
> import System.Environment (getArgs, getProgName)
> import System.Exit (exitSuccess, exitFailure)
> import System.IO (hPutStrLn, stderr)
> import Control.Applicative (Applicative(..))
> import Control.Monad (liftM, ap)
> import Data.List (unfoldr, isPrefixOf)

We will separate the ``print`` example program in *Software Tools* into several utilities. I don't have access to a real line printer (are these even made anymore? I can't find any info) so I'll start by building a "virtual" line printer. A line printer consumes lines of text and prints them onto paper one by one. Our virtual line printer should do the same, or something like it -- consume lines of text and convert them to a format that can be sent to a real printer.

*PostScript* is a programming language, in use since the mid-1980s, which allows us to succinctly describe the appearance of a printed page. Many printers can directly interpret programs written in PostScript and there is a large ecosystem of tools which can manipulate PostScript documents. The language is a de facto standard, and so we choose PostScript as the output format of our virtual line printer, ``pslineprint``.


About PostScript
----------------

PostScript is a very mature stack-oriented programming language, described in the [PostScript Language Reference Manual](https://www.adobe.com/products/postscript/pdfs/PLRM.pdf). We will only need to use a few features of the language: to print text (including strange characters) using a specific typeface to specific locations on a page and to print multiple pages.

Every PS document must start with the line

    %!PS

Then to print text we have to select a font.

    /Courier findfont
    12 scalefont
    setfont

Every point on the page has a pair of coordinates; the lower left corner of the page is $(0,0)$, and $(h,k)$ is $h$ points from the left edge and $k$ points from the bottom edge. At any given time while a PostScript program is running there is a "current" position where all drawing commands are carried out; we can change the current position with ``moveto``. For example the following command moves the position to $(10,20)$.

    10 20 moveto

This line pushes the numbers 10 and 20 onto a virtual stack, and then ``moveto`` pops the first two items (which are numbers) off of the stack and has the side effect of moving the current position to those coordinates. (A full discussion of [stack-oriented languages](https://en.wikipedia.org/wiki/Stack-oriented_programming_language) is beyond our scope, but they are a very interesting topic and are very amenable to code generation.)

The ``show`` command prints a string at the current position using the current font; it even implicitly updates the current position so that multiple ``show`` commands work as expected. To actually render drawing commands to the page, we use ``showpage``, and ``%%Page:`` starts a new page. (That last command is not clear to me, but my PostScript viewer requires it.) Putting this together, try copying the following to a file called ``test.ps`` and opening it in a PostScript viewer. (Note that the file must end with a newline!)

    %!PS
    /Courier findfont
    12 scalefont
    setfont

    %%Page: 1
    10 20 moveto
    (hello world!) show
    showpage

    %%Page: 2
    10 20 moveto
    (what is this) show
    showpage

Okay. But there is one major limitation of PostScript that we'll have to work around: PostScript does not play very nicely with Unicode. The ``show`` function only behaves as expected on 8-bit ASCII text. The workaround is to use the function ``glyphshow``, which takes special symbolic names for glyphs escaped with a forward slash. For instance,

    /alpha glyphshow

prints the greek letter alpha as long as the current font has a glyph for it. (The version of Courier on my system does not have glyphs for very many special characters, so I will instead use ``FreeMono`` from the [GNU Foundation](https://www.gnu.org/software/freefont/).) Julian Wiseman has compiled a nice [table of PostScript glyph names](http://www.jdawiseman.com/papers/trivia/character-entities.html) ([archive link](https://web.archive.org/web/20160315094516/http://jdawiseman.com/papers/trivia/character-entities.html)).

> unicodeToPS :: String -> String
> unicodeToPS = renderPSText . toPSText
> 
> 
> data PSChar
>   = Plain String
>   | Glyph String
>   deriving (Show)
> 
> type PSText = [PSChar]
> 
> 
> renderPSText :: PSText -> String
> renderPSText = concatMap renderPSChar
>   where
>     renderPSChar :: PSChar -> String
>     renderPSChar (Plain s)
>       = "(" ++ s ++ ") show\n"
>     renderPSChar (Glyph g)
>       = "/" ++ g ++ " glyphshow\n"
> 
> 
> toPSText :: String -> PSText
> toPSText = condense . map toPSChar
>   where
>     condense :: PSText -> PSText
>     condense = unfoldr first
> 
>     first :: PSText -> Maybe (PSChar, PSText)
>     first [] = Nothing
>     first (x:xs) = case x of
>       Glyph g -> Just (Glyph g, xs)
>       Plain c -> do
>         let (ps,rest) = span isPlain xs
>         cs <- fmap concat $ sequence $ map fromPlain ps
>         Just (Plain (c++cs), rest)
> 
>     isPlain :: PSChar -> Bool
>     isPlain (Plain _) = True
>     isPlain (Glyph _) = False
> 
>     fromPlain :: PSChar -> Maybe String
>     fromPlain (Plain s) = Just s
>     fromPlain (Glyph _) = Nothing
> 
> 
> -- hold on to your butts
> toPSChar :: Char -> PSChar
> toPSChar x = case x of
>   '\\'     -> Plain "\\\\"
> 
>   -- Greek Letters: Uppercase
>   '\x0391' -> Glyph "Alpha"
>   '\x0392' -> Glyph "Beta"
>   '\x0393' -> Glyph "Gamma"
>   '\x0394' -> Glyph "Deltagreek"
>   '\x0395' -> Glyph "Epsilon"
>   '\x0396' -> Glyph "Zeta"
>   '\x0397' -> Glyph "Eta"
>   '\x0398' -> Glyph "Theta"
>   '\x0399' -> Glyph "Iota"
>   '\x039a' -> Glyph "Kappa"
>   '\x039b' -> Glyph "Lambda"
>   '\x039c' -> Glyph "Mu"
>   '\x039d' -> Glyph "Nu"
>   '\x039e' -> Glyph "Xi"
>   '\x039f' -> Glyph "Omicron"
>   '\x03a0' -> Glyph "Pi"
>   '\x03a1' -> Glyph "Rho"
>   '\x03a3' -> Glyph "Sigma"
>   '\x03a4' -> Glyph "Tau"
>   '\x03a5' -> Glyph "Upsilon"
>   '\x03a6' -> Glyph "Phi"
>   '\x03a7' -> Glyph "Chi"
>   '\x03a8' -> Glyph "Psi"
>   '\x03a9' -> Glyph "Omegagreek"
> 
>   -- Greek letters: Lowercase
>   '\x03b1' -> Glyph "alpha"
>   '\x03b2' -> Glyph "beta"
>   '\x03b3' -> Glyph "gamma"
>   '\x03b4' -> Glyph "delta"
>   '\x03b5' -> Glyph "epsilon"
>   '\x03b6' -> Glyph "zeta"
>   '\x03b7' -> Glyph "eta"
>   '\x03b8' -> Glyph "theta"
>   '\x03b9' -> Glyph "iota"
>   '\x03ba' -> Glyph "kappa"
>   '\x03bb' -> Glyph "lambda"
>   '\x03bc' -> Glyph "mugreek"
>   '\x03bd' -> Glyph "nu"
>   '\x03be' -> Glyph "xi"
>   '\x03bf' -> Glyph "omicron"
>   '\x03c0' -> Glyph "pi"
>   '\x03c1' -> Glyph "rho"
>   '\x03c2' -> Glyph "sigmafinal"
>   '\x03c3' -> Glyph "sigma"
>   '\x03c4' -> Glyph "tau"
>   '\x03c5' -> Glyph "upsilon"
>   '\x03c6' -> Glyph "phi"
>   '\x03c7' -> Glyph "chi"
>   '\x03c8' -> Glyph "psi"
>   '\x03c9' -> Glyph "omega"
> 
>   -- Otherwise
>   _        -> Plain [x]

First, we'll write a black-box module that exports only one function, ``unicodeToPS``, with the sole purpose of taking a string of unicode characters and returning the PostScript code needed to print it. The implementation of ``unicodeToPS`` is straigtforward, but tedious; we march down the string and chop it into ASCII and non-ASCII parts. The ASCII parts are handled with ``show`` and the non-ASCII parts handled one character at a time with ``glyphshow``.


Limiting the Scope
------------------

Before writing any code for the printer itself, let's decide what it will and will not do:

* It **will** print lines of unformatted unicode text in a fixed-width font (as nature intended).
* It **will not** worry about wrapping lines. If we try to print a line that is too long for the page, it will silently march off the edge.
* It **will not** worry about page headings or page numbers.
* It **will not** print multiple files -- only lines from ``stdin``.
* It **will not** interpret escape codes or formatting commands.

All of the "will not" tasks will be left for other tools to deal with; the virtual printer itself will be as simple as possible.


Modeling a Printer
------------------

Now for the virtual line printer. We will think of a line printer as a machine which prints lines in the context of some basic internal state. Some state we can think of as configurable, but fixed: page margins, font size, line spacing, and page size. We use an extremely basic model of page geometry. Other state is updated as the line printer prints lines: the current page number and the current line number. (The ``pageInProcess`` flag is set whenever the current page has text printed on it; this is needed later.)

> data Geom = Geom
>   { fontSize   :: Int
>   , lineSkip   :: Int
>   , vMargin    :: Int
>   , hMargin    :: Int
>   , pageHeight :: Int
>   , pageWidth  :: Int
>   } deriving (Show)
> 
> -- letter size, 12 pt type
> defaultGeom :: Geom
> defaultGeom = Geom
>   { fontSize   = 12
>   , lineSkip   = 2
>   , vMargin    = 28
>   , hMargin    = 32
>   , pageHeight = 792
>   , pageWidth  = 612
>   }
> 
> 
> data LPState = LPState
>   { pageSettings  :: Geom
>   , currentLine   :: Int
>   , currentPage   :: Int
>   , pageInProcess :: Bool
>   }
> 
> 
> makeLPState :: Geom -> LPState
> makeLPState geom  = LPState
>   { pageSettings  = geom
>   , currentLine   = 1
>   , currentPage   = 1
>   , pageInProcess = False
>   }

From the page geometry, we can compute two important quantities: the number of lines that can be printed on one page, and the position on the page of each line.

> numLinesPerPage :: Geom -> Int
> numLinesPerPage geom = floor ((pH - (2*vM)) / (fS + lS))
>   where
>     pH = fromIntegral $ pageHeight geom
>     vM = fromIntegral $ vMargin geom
>     fS = fromIntegral $ fontSize geom
>     lS = fromIntegral $ lineSkip geom
> 
> -- lower left corner of line number k
> lineStartPos :: Geom -> Int -> (Int,Int)
> lineStartPos geom k = (hM, pH - vM - k*(fS + lS))
>   where
>     hM = hMargin geom
>     vM = vMargin geom
>     pH = pageHeight geom
>     fS = fontSize geom
>     lS = lineSkip geom

We'd like to expose a small number of primitive commands that the printer accepts: print a line of text, advance to the next line or the next page. This problem is well modeled by a monad. We use a custom monad stack with explicit state and IO.

> newtype LinePrinter t = LP
>   { runLP :: LPState -> IO (t, LPState) }
> 
> runLPJob :: Geom -> LinePrinter t -> IO t
> runLPJob geom pr = do
>   (x,_) <- runLP pr (makeLPState geom)
>   return x
> 
> instance Monad LinePrinter where
>   return x = LP (\st -> return (x, st))
> 
>   x >>= f = LP foo
>     where
>       foo st1 = do
>         (y,st2) <- runLP x st1
>         runLP (f y) st2
> 
> -- (necessary)
> instance Applicative LinePrinter where
>   pure = return
>   (<*>) = ap
> 
> instance Functor LinePrinter where
>   fmap = liftM

Now the printer interface we expose is a small number of monadic functions. For instance, ``lpPutStr`` prints a string at the current line.

> lpPutStr :: String -> LinePrinter ()
> lpPutStr ""  = return ()
> lpPutStr str = lpStartPage >> LP write
>   where
>     write st = do
>       let (x,y) = lineStartPos (pageSettings st) (currentLine st)
>       putStrLn $ show x ++ " " ++ show y ++ " moveto"
>       putStr $ unicodeToPS str
>       return ((), st)

``lpLineFeed`` advances the "print head" to the next line.

> lpLineFeed :: LinePrinter ()
> lpLineFeed = lpStartPage >> LP lf
>   where
>     lf st = do
>       let
>         (kOld,mOld) = (currentLine st, currentPage st)
>         lpp = numLinesPerPage (pageSettings st)
> 
>       if kOld + 1 > lpp
>         then do
>           putStrLn "showpage\n"
>           return ((), st {currentLine = 1, currentPage = mOld+1, pageInProcess = False})
>         else do
>           return ((), st {currentLine = kOld+1, currentPage = mOld})
> 
> 
> lpPutStrLn :: String -> LinePrinter ()
> lpPutStrLn str = do
>   lpPutStr str
>   lpLineFeed

> lpInitialize :: LinePrinter ()
> lpInitialize = LP init
>   where
>     init st = do
>       putStrLn "%!PS"
>       putStrLn "/FreeMono findfont"
>       let k = fontSize $ pageSettings st
>       putStrLn $ show k ++ " scalefont"
>       putStrLn "setfont\n"
>       return ((), st)
> 
> lpStartPage :: LinePrinter ()
> lpStartPage = LP sp
>   where
>     sp st = do
>       if pageInProcess st == True
>         then return ()
>         else putStrLn $ "%%Page: " ++ show (currentPage st)
>       return ((), st { pageInProcess = True })
> 
> lpShutDown :: LinePrinter ()
> lpShutDown = LP sd
>   where
>     sd st = do
>         if pageInProcess st == False
>           then return ()
>           else putStrLn "showpage"
>         return ((), st { pageInProcess = False })

Putting these together, the ``lpPrintLns`` function prints a list of lines.

> lpPrintLns :: [String] -> LinePrinter ()
> lpPrintLns lns = do
>   lpInitialize
>   mapM_ lpPutStrLn lns
>   lpShutDown

> lpPutCCStrLn :: CCLine -> LinePrinter ()
> lpPutCCStrLn x = do
>   mapM_ lpPutStr (fromCCLine x)
>   lpLineFeed
> 
> lpPrintCCLns :: [CCLine] -> LinePrinter ()
> lpPrintCCLns lns = do
>   lpInitialize
>   mapM_ lpPutCCStrLn lns
>   lpShutDown

It is straightforward to write versions of ``lpPutStr`` and ``lpPrintLns`` that work on carriage control encoded lines we worked with in ``linecount`` -- doing so allows our virtual line printer to produce overstruck characters.


The Main Program
----------------

All we've built so far is a small monadic language which simulates a line printer; all the complexity of PostScript (and integrating unicode with PostScript) is hidden away behind the ``LinePrinter`` interface. Next we need to wire this language to the command line so it can interact seamlessly with our other tools.

This tool differs from the others we've built so far in that our virtual line printer has a few different knobs the user may want to adjust: specifically, the page geometry parameters. To make our tool unopinionated, we should expose these parameters to the user at the command line. And to minimize the burden on the user the order in which these parameters are specified should not matter. Handling several different possible options in any order *by hand* is tedious and error prone, so we will instead use the standard ``GetOpt`` library. This library allows us to declaratively specify what options our program has and provides several useful functions for reading and processing those options. For programs with very simple parameters the full power of ``GetOpt`` is overkill, but it is appropriate here.

The main program logic is very simple. We read the command line options, interpret them as a page geometry specification, and the run our monadic line printer on ``stdin``.

> main :: IO ()
> main = do
>   args <- getArgs
> 
>   let
>     argErr  = reportErrorMsgs [usageInfo "options" options]
>     corrErr = reportErrorMsgs ["corrupt input"]
> 
>   -- read options
>   flags <- case getOpt Permute options args of
>     (opts, [], []) -> return $ foldl (>>=) (Just defaultFlags) opts
>     otherwise      -> argErr >> exitFailure
> 
>   -- process options
>   (geom, mode) <- case flags of
>     Nothing -> argErr >> exitFailure
>     Just fs -> do
>       let
>         g = defaultGeom
>           { fontSize = fFontSize fs
>           , lineSkip = fLineSkip fs
>           , vMargin  = fVMargin fs
>           , hMargin  = fHMargin fs
>           }
> 
>       return (g, fMode fs)
> 
>   stdin <- getContents
> 
>   case mode of
>     Lines -> runLPJob geom $ lpPrintLns $ getLines stdin
> 
>     ASACC -> case readCCLines stdin of
>       Nothing -> corrErr >> exitFailure
>       Just xs -> runLPJob geom $ lpPrintCCLns xs
> 
>   exitSuccess
> 
> 
> {- Options -}
> 
> data Mode = Lines | ASACC
> 
> data Flags = Flags
>   { fFontSize :: Int
>   , fLineSkip :: Int
>   , fVMargin  :: Int
>   , fHMargin  :: Int
>   , fMode     :: Mode
>   }
> 
> 
> defaultFlags :: Flags
> defaultFlags = Flags
>   { fFontSize = 12
>   , fLineSkip = 2
>   , fVMargin  = 32
>   , fHMargin  = 28
>   , fMode     = Lines
>   }
> 
> 
> options :: [OptDescr (Flags -> Maybe Flags)]
> options =
>   [ Option [] ["font-size"]
>       (ReqArg readFontSize "INT")
>       "font size in points"
> 
>   , Option [] ["line-skip"]
>       (ReqArg readLineSkip "INT")
>       "line spacing in points"
> 
>   , Option [] ["vmargin"]
>       (ReqArg readVMargin "INT")
>       "vertical page margins in points"
> 
>   , Option [] ["hmargin"]
>       (ReqArg readHMargin "INT")
>       "left page margin in points"
> 
>   , Option [] ["asacc"]
>       (NoArg (\opts -> Just $ opts { fMode = ASACC }))
>       "interpret basic ASA carriage control codes"
>   ]
>   where
>     readFontSize str opts = do
>       k <- readDecimalNat str
>       return $ opts { fFontSize = k }
> 
>     readLineSkip str opts = do
>       k <- readDecimalNat str
>       return $ opts { fLineSkip = k }
> 
>     readVMargin str opts = do
>       k <- readDecimalNat str
>       return $ opts { fVMargin = k }
> 
>     readHMargin str opts = do
>       k <- readDecimalNat str
>       return $ opts { fHMargin = k }

Unlike our other tools, it is not so easy to write automated tests of a program like this. As an example, though, try running the following pipeline:

    sth-echo "hello\b\b\b\b\b_____" "world!"
     | sth-unescape
     | sth-overstrike
     | sth-pslineprint --asacc
     > psprinttest.ps

This should produce a page with two lines: the first with the word "hello" underlined.

When every program operates on plain text, making minimal assumptions about formats, it is easy to chain them together to perform complex tasks. Later on we will write programs to make the output of ``pslineprint`` prettier: line wrapping, pagination, and so on. By keeping this functionality out of the printer itself, all programs can stay small and modular.

Later, we may find occasion to enhance our virtual line printer with the ability to change to a bold or italicized font. Because of the modular, monadic design, this will be straightforward.


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
> unfoldrMaybe :: (b -> Maybe (Maybe (a,b))) -> b -> Maybe [a]
> unfoldrMaybe f x = case f x of
>   Nothing -> Nothing
>   Just Nothing -> Just []
>   Just (Just (a,b)) -> do
>     as <- unfoldrMaybe f b
>     Just (a:as)
>
>
> data CCLine
>   = CCLine [String]
>   deriving (Show)
> 
> fromCCLine :: CCLine -> [String]
> fromCCLine (CCLine xs) = xs
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
