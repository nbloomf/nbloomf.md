---
title: Software Tools in Haskell: entab, echo, overstrike
author: nbloomf
date: 2016-02-27
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.


<a name="entab" />

## ``entab``: replace spaces on stdin with tabs

The ``detab`` program replaced tab characters with spaces, taking arguments at the command line to let the user specify the width of the tab stops. The ``entab`` program reverses this process. It takes input which we assume represents some tabular data where different columns start on specific character columns, chops the input lines into columns, and replaces any trailing spaces in a given column by a single ``\t`` character. Just like ``detab``, the default tab stop width is 8, and we allow the user to specify a list of tab stop widths at the command line with the convention that the *last* user-specified width is assumed to repeat indefinitely.

The basic structure of this program is nearly identical to that of ``detab`` (which is not surprising).


```haskell
-- sth-entab: replace spaces on stdin with tabs
--   line-oriented

module Main where

import SoftwareTools.Lib
  ((>>>), exitSuccess, exitFailure, getArgs)
import SoftwareTools.Lib.IO    (lineFilter)
import SoftwareTools.Lib.Read  (readPosIntList)
import SoftwareTools.Lib.Text  (getLines)
import SoftwareTools.Lib.List  (spanAtMostWhile, padToByAfter)
import SoftwareTools.Lib.Error (reportErrorMsgs)


main :: IO ()
main = do
  args <- getArgs

  -- Read positive integer tabstop arguments.
  -- Default is [8].
  ts <- case readPosIntList args of
    Just [] -> return [8]
    Just ks -> return ks
    Nothing -> reportErrorMsgs
                 ["tab widths must be positive integers."
                 ] >> exitFailure

  -- Do it!
  lineFilter (insertTabStops ts)
  exitSuccess
```


We reuse the functions for reading lists of nonnegative integers that we wrote for ``detab``. The heavly lifting is done by ``insertTabStops``.


```haskell
insertTabStops :: [Int] -> String -> String
insertTabStops [] xs = xs
insertTabStops ks xs = accum [] ks xs
  where
    accum zs _ "" = concat $ reverse zs
    accum zs [t] ys =
      let (as,bs) = splitColumn t ys in
      accum (as:zs) [t] bs
    accum zs (t:ts) ys =
      let (as,bs) = splitColumn t ys in
      accum (as:zs) ts bs

    splitColumn :: Int -> String -> (String, String)
    splitColumn k xs
      | k  <= 0   = (xs,"")
      | xs == ""  = ("","")
      | otherwise = (ds,bs)
          where
            (as,bs) = splitAt k xs
            munch = dropWhile (== ' ')
            cs = reverse as
            ds = if bs == ""
                     then let es = reverse $ munch cs in
                       if es == "" then "\t" else es
                     else case cs of
                       ' ':_ -> reverse ('\t':(munch cs))
                       otherwise -> as
```


Even the shape of this function on the page resembles that of its counterpart from ``detab``. Note the use of an accumulating parameter helper function.

In Exercise 2-2, Kernighan and Plauger ask us to make the simplest change to ``entab`` to make it handle tabs correctly. After thinking about this, I've decided the right thing to do is **nothing**. Let's imagine what it means if the user is trying to use ``entab`` on data that contains tabs. I can think of two possible situations.

1. The tabs are "semantic tabs", used to delimit data. That is, the input either is already tab-delimited, or contains a mixture of tab-delimited and column-delimited data. In this case the user has other problems. The right thing to do in the first case is nothing, and in the second case depends on the user's intent. We could assume that a semantic tab means "advance to the next tab stop", but this now changes the column indices of the characters in the remainder of the line unpredictably, so the intent of any tab stop width input is unclear. It would be better here to run the data through ``detab`` first to remove the tabs, then run through ``entab`` to put them back.
2. The tabs are "literal tabs", as in the data itself involves tab characters for some reason, and they have a different meaning in whatever context the user cares about. This is, after all, a valid reason to use a column-delimited format. Of course in this case the right thing to do is leave the tabs alone.

If we ignore tabs altogether, then at best this is the Right Thing and at worst the user has to use ``detab`` first (or has other problems). On the other hand, trying to make ``entab`` do something useful with tabs would make the program more complicated (and probably clutter the interface) with little benefit.



<a name="echo" />

## ``echo``: write arguments to stdout

All the programs we've written so far are strictly *filters*: they read data from stdin and write data to stdout. The metaphor here is that small programs are chained together in a larger "pipeline", and data flows from one end to the other; along the way, each filter changes the data in some way. By reading and writing from stdin and stdout, individual programs do not need to worry about where their data comes from and goes.

``echo`` is the first program we've written that *produces* data without needing to take any from stdin; it is a *source*. (The converse, a program which consumes data without producing any, is a *sink*). ``echo`` simply takes a list of arguments at the command line and writes them to stdout. Unlike the standard echo, we write the arguments one per line.


```haskell
-- sth-echo: write arguments to stdout, one per line

module Main where

import SoftwareTools.Lib (getArgs, exitSuccess)
import SoftwareTools.Lib.IO (putStrLns)

main :: IO ()
main = getArgs >>= putStrLns >> exitSuccess
```


We can now use ``echo`` to test our other programs. For instance, using the shell to run


```
sth-echo "hello" | sth-charcount
```


prints ``6`` to the terminal. Woo!



<a name="overstrike" />

## ``overstrike``: interpret backspaces using line printer control codes

At first I was going to skip this program, because I cannot imagine myself having a use for it. But I started thinking about the problem and before I knew it the program was written, so I might as well write about it. :)

In ASCII (and unicode) there is a backspace control character. This character is only kind of related to the backspace key on a modern keyboard. On a typewriter, the backspace key physically moves the carriage "back" one "space", without erasing any characters that might already be printed there. This allowed the typist to physically print one character on top of another, called *overstriking*. Doing so allowed for things like underlining words (overstrike with underscore), striking out words (overstrike with hyphen), creating new characters (overstrike hyphen and colon to get a division sign, maybe), and elaborate typewriter art (a precursor of ASCII art). For example, the literal sequence of key strokes

    Hello world!\b\b\b\b\b\b\b\b\b\b\b\b____________

would appear on the page as underlined text.

According to Kernighan and Plauger, line printers (I've unfortunately never used one, so I'll take their word for it) can achieve overstriking by not advancing the paper between lines. On some machines this was done by prepending each line to be printed with a control code: either a space or a plus sign. For instance, the lines

     Hello world!
    +____________

would be printed one on top of the other, effectively underlining "Hello world!". A space at the beginning of the line means "advance the paper to the next line", and a plus sign means "don't".

The ``overstrike`` program turns a sequence of typewriter-style keystrokes into a sequence of line printer-style print commands. Our strategy is this: every character to be printed has an associated *column index*; this is the column where that character belongs. For instance, in the line

    abcde

The character ``a`` has column index 1, ``b`` has column index 2, and so on. (That's right, I think of strings as 1-indexed. What's it to ya?) Anyway, normally the next character in the string has column index one more than the one before it. Except for those pesky backspace characters! They decrement (by two, really) the column index of everything that comes after them (unless the index is 1, since we cannot print to the left of the left edge of a line). So in the line

    abcde\b\b\bfg

the character ``a`` has index 1, ``b`` is 2, ``c`` is 3, ``d`` is 4, ``e`` is 5, ``f`` is **3**, and ``g`` is **4**.

The trick is this: we can march down a string and determine the column index of every non-backspace character. This results in a big list of char-int pairs. Now in principle each one of these can be turned into an overstrike line. For instance, the last example could be expressed as

     a
    + b
    +  c
    +   d
    +    e
    +  f
    +   g

But there is a problem here: while correct, having only one printed character per line is extremely inefficient! If two lines do not "overlap", they can be merged. So a more efficient way to achieve the same effect is with

     abcde
    +  fg

In fact this is a *most* efficient set of overstrike lines, since 2 is the minimal number of lines required. It isn't too hard to see that if a given line has at most $k$ characters with the same column index, then $k$ is the minimum number of overstrike lines required to render that line (and there is always a set of $k$ overstrike lines that works). Why? We can think of this as a graph coloring problem. The char-int pairs are vertices (ignoring those where the character is a blank), and two vertices are adjacent if they have the same column index. Colorings of this graph correspond to valid sets of overstrike lines. But this graph is a disjoint union of complete graphs, with one component for each column index. The minimum number of colors required is the size of the largest component.

To identify a coloring of the char-int graph, we (1) drop all the blanks, (2) sort the list by column index, and (3) split the list into maximal subsequences by column index. (What?) Finally, (4) thinking of these char-int pairs as sparse lists, convert to real actual lists, using space characters for any missing indices.


```haskell
overstrike :: String -> String
overstrike = overstrikeLines
  >>> zipWith (:) (' ' : (repeat '+'))
  >>> intercalate "\n"

overstrikeLines :: String -> [String]
overstrikeLines =
  columnIndices
    >>> filter (\(c,_) -> c /= ' ')          -- try omitting
    >>> sortBy (\(_,a) (_,b) -> compare a b) -- these lines
    >>> maxMonoSubseqsBy p
    >>> map (fromSparseList ' ')
  where
    p u v = if snd u < snd v
              then True else False

    -- Assign a column index 
    columnIndices :: String -> [(Char,Int)]
    columnIndices = accum [] 1
      where
        accum zs _ ""     = reverse zs
        accum zs k (c:cs) = case c of
          '\b'      -> accum zs (max 1 (k-1)) cs
          otherwise -> accum ((c,k):zs) (k+1) cs

maxMonoSubseqsBy :: (a -> a -> Bool) -> [a] -> [[a]]
maxMonoSubseqsBy p = unfoldr maxMonoSubseq
  where
    maxMonoSubseq [] = Nothing
    maxMonoSubseq xs = accum [] [] xs

    accum as bs [] = Just (reverse as, reverse bs)
    accum [] bs (z:zs) = accum [z] bs zs
    accum (a:as) bs (z:zs) = if p a z
      then accum (z:a:as) bs zs
      else accum (a:as) (z:bs) zs

fromSparseList :: a -> [(a,Int)] -> [a]
fromSparseList x [] = []
fromSparseList x ys = accum 1 [] ys
  where
    accum _ as [] = reverse as
    accum t as ((z,h):zs) = case compare t h of
      EQ -> accum (t+1) (z:as) zs
      LT -> accum (t+1) (x:as) ((z,h):zs)
      GT -> accum (t+1) as zs
```


As an aside: I pulled out ``maxMonoSubseqsBy`` and ``fromSparseList`` as abstractly as possible. When writing Haskell (this is probably true in other languages as well) writing code with the most general possible type usually makes it **easier** to write. Working with a less specific type means there are fewer meaningful things to say, and when there are fewer paths to choose from the correct one is easier to find. This code, for instance, was nearly written in one pass with no substantial editing needed. Not because I am particularly good but because **there's essentially only one way to do it**. Pick a type signature and a recursion pattern (here, either ``unfoldr`` or accumulating parameter) and the rest practically writes itself.

After all that, the main program is pretty straightforward.


```haskell
-- sth-overstrike: interpret backspaces using line printer control codes
--   line-oriented

module Main where

import SoftwareTools.Lib
  ((>>>), exitSuccess, sortBy, intercalate)
import SoftwareTools.Lib.IO
  (lineFilter)
import SoftwareTools.Lib.List
  (maxMonoSubseqsBy, fromSparseList)
import SoftwareTools.Lib.Text
  (getLines)


main :: IO ()
main = do
  lineFilter overstrike
  exitSuccess
```
