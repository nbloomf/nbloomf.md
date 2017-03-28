---
title: Software Tools in Haskell: unescape
subtitle: interpret C and ASCII escape codes on stdin
date: 2016-02-21
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-unescape: interpret C and ASCII backslash escape codes on stdin
> module Main where
> 
> import System.Exit (exitSuccess)

See also the [Backslash](/posts/software-tools-in-haskell/Lib/Backslash.html) module.

> import Lib.Backslash (bsUnEsc)

While testing the [``overstrike``](/posts/2016-02-20-software-tools-in-haskell-overstrike.html) program I ran into an inconvenient problem: I couldn't find an easy and consistent way to type control characters (namely backspace, but others have the same problem) that works both in my terminal and in my golden test suite. It seems like every program -- the terminal, the shell, the test runner -- wants to interpret these characters slightly differently. This problem is a good candidate for a filter-style program. ``unescape`` reads lines from stdin and interprets any C-style escape sequences or ASCII abbreviations it finds. (There is a nice wiki page on [C-style escape sequences](https://en.wikipedia.org/wiki/Escape_sequences_in_C), and the page on [ASCII](https://en.wikipedia.org/wiki/ASCII#ASCII_control_code_chart) includes a table of abbreviations.)

The main program is simple enough, as it simply munches through the lines on stdin looking for escape codes.

> main :: IO ()
> main = do
>   charFilter bsUnEsc
>   exitSuccess

The real work is done by the library function ``bsUnEsc``.


Old stuff
---------

> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
