---
title: Software Tools in Haskell: detab
author: nbloomf
date: 2016-02-25
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.


<a name="detab" />

## ``detab``: replace tabs on stdin with spaces

The tab key on modern computer keyboards is a holdover from mechanical typewriters where it allows the typist to advance the carriage to the next of several fixed columns, called *tab stops*, with a single key press. On many mechanical (and electric!) typewriters the positions of these tab stops are adjustable, which is useful for typing strictly formatted documents like letters and forms. The semantics of tab as a kind of "advance" command have turned out to be useful in other contexts like web browsers (where tab may cycle through the links on a page) and graphical user interfaces (where tab may cycle through manipulable widgets in a gui).

In a text file, the exact interpretation of ``\t`` characters depends on what is doing the interpreting. Most interactive text editors imitate typewriters by implementing tab stops of a fixed (and maybe user-adjustable) width, while spreadsheet editors use tab and newline to delimit tabular data.

This program allows the user to treat tab stops in a system-independent way (assuming a fixed-width font) by replacing ``\t`` characters (which are subjective) with spaces (which are not). It will take a list of tab stop widths at the command line and then replace ``\t``s with however many spaces are needed to advance to the next tab stop.

For example, invoking ``detab 10`` with the file

    hello\tworld
    hola\tmundo
    hela\tvelt

should produce the output

    hello     world
    hola      mundo
    hela      velt

As usual we need to make some assumptions. Also as usual, unicode makes things more complicated.

* The input consists of lines, separated by ``\n``s, each of which has several fields, separated by ``\t``s. The final output line will be terminated by a newline, even if the final input line was not.
* Tab stop widths are always positive. If none are provided, all tab stop widths default to 8.
* We will assume that each character (other than tabs and newlines) takes one "character cell". **This assumption is wrong.** Unicode includes zero-width characters like combining diacritics as well as characters that are typically rendered as double-width, like many CJK characters. Taking this into account would be complicated, so we won't. (This isn't *so* bad. We can write filter programs later that replace combining diacritics with precomposed versions, and which replace halfwidth characters with fullwidth equivalents. Because "most" text files include only characters within one language, these three tools together should be able to handle "most" real text.)
* By default, all tab stops will be eight character cells wide. To avoid making our program unnecessarily opinionated, the user can specify a sequence of tab stop widths at the command line. We then have to decide what to do if a line of input text has more tabs than the user provided tab stop widths. For example, if the user invokes ``detab 8 10 12`` on an input line with 5 ``\t``s, what should be the widths of tab stops 4 and 5? I see a few possible ways to resolve this.
    1. Unspecified tab stop widths cause an error. (Maybe not terrible; if the user is specifying individual tab stop widths they probably have very specifically formatted data. But we'd like to avoid failing if possible.)
    2. Unspecified tab stop widths are ignored, perhaps by leaving the ``\t`` characters alone, or by removing them, or even by truncating the input. (Bad; probably violates the user's intent.)
    3. Unspecified tab stop widths are some built in constant width, like 8. (Bad for obvious reasons.)
    4. Unspecified tab stop widths are some user-configurable constant width, say with an extra argument at the command line. (Bad; clutters up the interface.)
    5. Tab stop widths cycle through the user-supplied values. E.g., ``detab 4 6 8`` formats with tab stops of width 4, 6, 8, 4, 6, 8, and so on. (Not great, since it is difficult to imagine that the most useful general solution to this problem has *custom* tab stop widths that *cycle*. But this idea is better than the previous in one respect: silently inferring intent is a good idea.)
    6. If the user provides any tab stop widths as arguments, we treat the *last* one as if it repeats indefinitely. E.g., ``detab 4 6 8`` formats with tab stops of width 4, 6, 8, 8, 8, 8, and so on. **This seems like the Right Thing To Do**. It gives the user total control, requires no special cases for the interface, and also elegantly handles the situation where the user wants all tab stops to have the same width. If we want tab stops of width 10, for instance, we invoke ``detab 10``.
* We also need to decide what to do if a given "column" of input text contains no tabs. Or, equivalently, if a given "tab cell" has too many characters. For example, if we interpret the input line ``helloworld\t`` using the default tab stop width of 8, in which tab-column is the ``\t``, the first or the second? Here we take inspiration from the typewriter heritage of tab: pressing tab advances to the *next* tab stop, wherever the carriage happens to be. It is not by default a "cell separator". So, for instance, invoking ``detab 4 10 8`` on ``hello\tworld`` puts 9 spaces between ``hello`` and ``world``.

This program is quite a bit more complicated than the ones we've written so far because it needs to take command line arguments from the user. That means parsing structured input (here, base 10 natural numbers) and the possibility of input errors. My version of this program is pretty long compared to the *Software Tools* example, but it does have extra functionality; namely custom tab stop widths.

First, here is the main program.


```haskell
module Main where

import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import Control.Arrow ((>>>))
import SoftwareTools.FunctionLibrary
  (getLines, convertTabStops, readPosIntList)


main :: IO ()
main = do
  args <- getArgs

  -- Read positive integer tabstop arguments.
  -- Default is [8].
  ts <- case readPosIntList args of
    Just [] -> return [8]
    Just ks -> return ks
    Nothing -> errorParsingArgs

  -- Detab a single line ln with tabstops ts.
  let detab ln = case convertTabStops ts ln of
                   Nothing -> errorDeTabbing ts ln
                   Just cs -> putStrLn cs

  -- Do it!
  getContents
    >>= (getLines >>> map detab >>> sequence_)
    >> exitSuccess
```


In order, we (1) get the user-supplied tab stop widths as strings (``getArgs``), then (2) parse these as positive integers (``readPosIntList``), which may fail. We have a custom library function (``convertTabStops``) that does the real work, and here (3) define a throwaway function ``detab`` that wraps ``convertTabStops`` and handles its error condition (more on that later). Finally, we (4) read from stdin lazily, split the input into lines, and apply ``detab`` to each one.

There are two error conditions: first, the user may provide bad command line arguments. In this case we gently remind the user how to use this program. The second error is more insidious: the ``convertTabStops`` function lives in the ``Maybe`` monad (more on that later). This usage "should" never return ``Nothing``, and if it does, there is a bug in the program. So we report the line and the tab stop sequence that caused a problem to aid in debugging. In both cases we follow the standard unix practice of writing errors to stderr rather than stdout.


```haskell
errorParsingArgs :: IO a
errorParsingArgs = do
  name <- getProgName
  hPutStrLn stderr $
    name ++ " error: tab widths must be positive natural numbers in base 10."
  exitFailure


-- This should not happen.
errorDeTabbing :: [Int] -> String -> IO a
errorDeTabbing ts ln = do
  name <- getProgName
  hPutStrLn stderr $ name ++ " error"
  hPutStrLn stderr $ "LINE: " ++ ln
  hPutStrLn stderr $ "TABS: " ++ show ts
  exitFailure
```


Okay, that is straightforward enough. But the real work happens in two functions, ``readPosIntList`` and ``convertTabStops``. First, reading natural numbers. These functions are general-purpose enough to go in the library.


```haskell
readPosIntList :: [String] -> Maybe [Int]
readPosIntList =
  sequence . map (guardMaybe (>0)) . map readDecimalNat


readDecimalNat :: String -> Maybe Int
readDecimalNat xs = do
  ys <- sequence $ map decToInt $ reverse xs
  return $ sum $ zipWith (*) ys [10^t | t <- [0..]]
  where
    decToInt :: Char -> Maybe Int
    decToInt x = lookup x
      [ ('0',0), ('1',1), ('2',2), ('3',3), ('4',4)
      , ('5',5), ('6',6), ('7',7), ('8',8), ('9',9)
      ]


guardMaybe :: (a -> Bool) -> Maybe a -> Maybe a
guardMaybe p x = do
  y <- x
  case p y of
    True  -> Just y
    False -> Nothing
```


``readDecimalNat`` takes a string of decimal digits and converts it to a natural number (negatives are not handled). Or, rather, converts to a ``Maybe Int``. Conversion will fail if the input string does not consist of only characters 0 through 9; in this case the function returns ``Nothing``. (We don't see an explicit ``Nothing`` in the code because it is implicitly returned by the standard library function ``lookup``.) Then ``readPosIntList`` simply applies ``readDecimalNat`` to a list of strings, and makes sure the numbers returned are all positive. This is where ``guardMaybe`` comes in.

Next we show ``convertTabStops``.


```haskell
convertTabStops :: [Int] -> String -> Maybe String
convertTabStops [] _  = Nothing
convertTabStops ks xs = accum [] ks xs
  where
    accum zs _   "" = Just $ concat $ reverse zs
    accum zs [t] ys = do
      (as,bs) <- splitTabStop t ys
      accum (as:zs) [t] bs
    accum zs (t:ts) ys = do
      (as,bs) <- splitTabStop t ys
      accum (as:zs) ts bs

    splitTabStop :: Int -> String -> Maybe (String, String)
    splitTabStop k xs
      | k <= 0    = Nothing
      | otherwise = do
          (as,bs) <- spanAtMostWhile k (/= '\t') xs
          cs      <- padToByAfter k ' ' as
          case bs of
            ""      -> return (cs,"")
            '\t':ds -> return (cs,ds)
            ds      -> return (cs,ds)


spanAtMostWhile :: Int -> (a -> Bool) -> [a] -> Maybe ([a],[a])
spanAtMostWhile k p xs
  | k < 0     = Nothing
  | otherwise = Just $ acc k [] xs
  where
    acc 0 as bs = (reverse as, bs)
    acc _ as [] = (reverse as, [])
    acc t as (b:bs) = if p b
      then acc (t-1) (b:as) bs
      else (reverse as, b:bs)


padToByAfter :: Int -> a -> [a] -> Maybe [a]
padToByAfter k z xs
  | k < 0     = Nothing
  | otherwise = acc k [] xs
  where
    acc 0 as [] = Just $ reverse as
    acc 0 _  _  = Nothing
    acc t as [] = Just $ reverse as ++ replicate t z
    acc t as (b:bs) = acc (t-1) (b:as) bs
```


The helper function ``splitTabStop`` takes a single tab stop width ``k`` and a string ``xs``, and peels of the first ``k`` characters of ``xs`` unless one of them is a ``\t``. It then returns a pair consisting of the peeled of characters and the remainder of the string. (If the ``k`` parameter is negative, we have a problem, so we return ``Nothing`` in this case. **This is why we have to handle the second error condition in the main function.** If Haskell had a convenient positive integer type, this could be dealt with differently.) Then ``convertTabStops`` simply marches down an entire line with a list of tab stop widths, peeling of tab stops as it goes. This is done using an accumulating parameter function, ``accum``. Once the string is empty, ``accum`` reverses the accumulating parameter and returns it (concatenated), otherwise it takes the next tab stop width and repeats.

``spanAtMostWhile`` is a combination of the standard library functions ``span`` and ``take``. It peels off up to ``k`` elements of a list provided they all satisfy predicate ``p`` and returns both the peeled off elements and the remainder of the list. ``padToByAfter`` pads lists to a given length with a given character, throwing an error if the given length is already too long. Both of these are general enough to factor out; they also both use the accumulating parameter style to avoid space leaks.
