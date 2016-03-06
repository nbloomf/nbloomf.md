---
title: Software Tools in Haskell: unescape, escape
author: nbloomf
date: 2016-02-29
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.

Today I feel like going off script. (These are not in *Software Tools*.)


<a name="unescape" />

## ``unescape``: interpret C and ASCII backslash escape codes on stdin

While testing the ``overstrike`` program, I ran into an inconvenient problem: I couldn't find an easy and consistent way to type control characters (namely backspace, but others have the same problem) that works both in my terminal and in my golden test suite. It seems like every program - the terminal, the shell, the test runner - wants to interpret these characters in its own way. This problem is a good candidate for a filter-style program. ``unescape`` reads lines from stdin and interprets any C-style escape sequences or ASCII abbreviations it finds. (There is a nice wiki page on [C-style escape sequences](https://en.wikipedia.org/wiki/Escape_sequences_in_C), and the page on [ASCII](https://en.wikipedia.org/wiki/ASCII#ASCII_control_code_chart) includes a table of abbreviations.)

The main program is simple enough, as it simply munches through the lines on stdin looking for escape codes.


```haskell
-- sth-unescape: interpret C and ASCII backslash escape codes on stdin
--   character-oriented

module Main where

import SoftwareTools.Lib
  (exitSuccess)
import SoftwareTools.Lib.IO
  (charFilter)
import SoftwareTools.Lib.Text
  (backslashUnEscape)


main :: IO ()
main = do
  charFilter backslashUnEscape
  exitSuccess
```


The real work is done by the library function ``backslashUnEscape``. There's no nice way to do this, so we pattern match on the prefix of a string looking for escape codes. One gotcha: the ASCII abbreviations are not prefix free; for instance the meaning of the string ``\SOHello`` is ambiguous; is it ``\SO`` (Shift Out) followed by ``Hello`` or ``\SOH`` (Start Of Heading) followed by ``ello``? To make sure these are detected correctly, we pattern match ``\SOH`` first (since otherwise that string would always match as ``\SO`` followed by ``H``) and add one more escape code, ``\&`` (taken from Haskell), for those occasions when you *really* want ``\SO`` followed by ``H`` not interpreted as ``\SOH``. ``\&`` represents the empty string, so we can do this with ``\SO\&H``. So, you know, for all those times you need carefully formatted ASCII control codes.

``backslashUnEscape`` is a library function because it will probably be useful later for parsing command line arguments.


```haskell
backslashUnEscape :: String -> String
backslashUnEscape = concat . unfoldr firstChar
  where
    firstChar :: String -> Maybe (String, String)
    firstChar "" = Nothing
    firstChar (c:cs) = case c of
      '\\' -> case cs of
        -- Basic C-style escape characters
        ('a' :ds) -> Just ("\a\&",ds)
        ('b' :ds) -> Just ("\b\&",ds)
        ('f' :ds) -> Just ("\f\&",ds)
        ('n' :ds) -> Just ("\n\&",ds)
        ('r' :ds) -> Just ("\r\&",ds)
        ('t' :ds) -> Just ("\t\&",ds)
        ('v' :ds) -> Just ("\v\&",ds)
        ('\\':ds) -> Just ("\\\&",ds)
        ('\'':ds) -> Just ("'\&" ,ds)
        ('"' :ds) -> Just ("\"\&",ds)
        ('?' :ds) -> Just ("?\&" ,ds)

        -- 3-digit octal ASCII codes
        ('0':k2:k3:ds) -> octalCode ['0',k2,k3] ds
        ('1':k2:k3:ds) -> octalCode ['1',k2,k3] ds
        ('2':k2:k3:ds) -> octalCode ['2',k2,k3] ds
        ('3':k2:k3:ds) -> octalCode ['3',k2,k3] ds
        ('4':k2:k3:ds) -> octalCode ['4',k2,k3] ds
        ('5':k2:k3:ds) -> octalCode ['5',k2,k3] ds
        ('6':k2:k3:ds) -> octalCode ['6',k2,k3] ds
        ('7':k2:k3:ds) -> octalCode ['7',k2,k3] ds

        -- 2-digit hex ASCII codes
        ('x':k1:k2:ds) -> case all isHexDigit digs of
          True  -> case readLitChar ("\\x" ++ digs) of
            []        -> Just ("\\x" ++ digs, ds)
            ((x,_):_) -> Just ([x],ds)
          False -> Just ("\\x" ++ digs, ds)
          where
            digs = [k1,k2]

        -- Standard ASCII abbreviations
        ('N':'U':'L':ds) -> Just ("\NUL\&", ds)
        ('S':'O':'H':ds) -> Just ("\SOH\&", ds)
        ('S':'T':'X':ds) -> Just ("\STX\&", ds)
        ('E':'T':'X':ds) -> Just ("\ETX\&", ds)
        ('E':'O':'T':ds) -> Just ("\EOT\&", ds)
        ('E':'N':'Q':ds) -> Just ("\ENQ\&", ds)
        ('A':'C':'K':ds) -> Just ("\ACK\&", ds)
        ('B':'E':'L':ds) -> Just ("\BEL\&", ds)
        ('D':'L':'E':ds) -> Just ("\DLE\&", ds)
        ('D':'C':'1':ds) -> Just ("\DC1\&", ds)
        ('D':'C':'2':ds) -> Just ("\DC2\&", ds)
        ('D':'C':'3':ds) -> Just ("\DC3\&", ds)
        ('D':'C':'4':ds) -> Just ("\DC4\&", ds)
        ('N':'A':'K':ds) -> Just ("\NAK\&", ds)
        ('S':'Y':'N':ds) -> Just ("\SYN\&", ds)
        ('E':'T':'B':ds) -> Just ("\ETB\&", ds)
        ('C':'A':'N':ds) -> Just ("\CAN\&", ds)
        ('S':'U':'B':ds) -> Just ("\SUB\&", ds)
        ('E':'S':'C':ds) -> Just ("\ESC\&", ds)
        ('D':'E':'L':ds) -> Just ("\DEL\&", ds)
        ('E':'M'    :ds) -> Just ("\EM\&",  ds)
        ('F':'S'    :ds) -> Just ("\FS\&",  ds)
        ('G':'S'    :ds) -> Just ("\GS\&",  ds)
        ('R':'S'    :ds) -> Just ("\RS\&",  ds)
        ('U':'S'    :ds) -> Just ("\US\&",  ds)
        ('S':'P'    :ds) -> Just ("\SP\&",  ds)
        ('B':'S'    :ds) -> Just ("\BS\&",  ds)
        ('H':'T'    :ds) -> Just ("\HT\&",  ds)
        ('L':'F'    :ds) -> Just ("\LF\&",  ds)
        ('V':'T'    :ds) -> Just ("\VT\&",  ds)
        ('F':'F'    :ds) -> Just ("\FF\&",  ds)
        ('C':'R'    :ds) -> Just ("\CR\&",  ds)
        ('S':'O'    :ds) -> Just ("\SO\&",  ds)
        ('S':'I'    :ds) -> Just ("\SI\&",  ds)

        -- C99-style universal character names
        ('u':k1:k2:k3:k4:ds) -> case all isHexDigit digs of
          True  -> case readLitChar ("\\x" ++ digs) of
            []        -> Just ("\\u" ++ digs, ds)
            ((x,_):_) -> Just ([x],ds)
          False -> Just ("\\u" ++ digs, ds)
          where
            digs = [k1,k2,k3,k4]

        ('U':k1:k2:k3:k4:k5:k6:k7:k8:ds) -> case all isHexDigit digs of
          True  -> case readLitChar ("\\x" ++ digs) of
            []        -> Just ("\\U" ++ digs, ds)
            ((x,_):_) -> Just ([x],ds)
          False -> Just ("\\U" ++ digs, ds)
          where
            digs = [k1,k2,k3,k4,k5,k6,k7,k8]

        -- stolen from haskell
        ('&':ds) -> Just ("",ds)

        -- If we don't see a valid esc code, just move on.
        ds -> Just ("\\\&", ds)

      -- No backslash
      otherwise -> Just ([c],cs)
      where
        isHexDigit :: Char -> Bool
        isHexDigit = (`elem` "0123456789aAbBcCdDeEfF")

        isOctDigit :: Char -> Bool
        isOctDigit = (`elem` "01234567")

        octalCode digs ds = case all isOctDigit digs of
          True  -> case readLitChar ("\\o" ++ digs) of
            []        -> Just ('\\':digs, ds)
            ((x,_):_) -> Just ([x],ds)
          False -> Just ('\\':digs, ds)
```



<a name="escape" />

## ``escape``: replace non-printable, non-ascii chars on stdin with c escape sequences

The ``escape`` program is the companion of ``unescape``; it replaces any non-printing, non-ASCII characters with C-style escape sequences using only visible ASCII.


```haskell
-- sth-escape: replace non-printable, non-ascii chars on stdin with c escape sequences
--   character-oriented

module Main where

import System.Exit (exitSuccess)
import STH.Lib (charFilter, bsEsc)


main :: IO ()
main = do
  charFilter bsEsc
  exitSuccess
```


The work is done by ``bsEsc``:

```haskell
bsEsc :: String -> String
bsEsc = concatMap esc

esc :: Char -> String
esc x
  | 32 <= k && k <= 126 = [x]
  | k == 7    = "\\a"
  | k == 8    = "\\b"
  | k == 9    = "\\t"
  | k == 10   = "\\n"
  | k == 11   = "\\v"
  | k == 12   = "\\f"
  | k == 13   = "\\r"
  | k == 27   = "\\e"
  | k < 256   = "\\x" ++ show2Hex k
  | k < 65536 = "\\u" ++ show4Hex k
  | otherwise = "\\U" ++ show8Hex k
  where
    k = ord x

    show2Hex t = reverse $ take 2 (reverse (showHex t) ++ (repeat '0'))
    show4Hex t = reverse $ take 4 (reverse (showHex t) ++ (repeat '0'))
    show8Hex t = reverse $ take 8 (reverse (showHex t) ++ (repeat '0'))
```


``showHex`` is a library function that returns the hexadecimal expansion of a natural number.


```haskell
showHex :: (Integral n) => n -> String
showHex n
  | n < 0  = '-' : showHex (-n)
  | n == 0 = "0"
  | otherwise = map toHexDigit (digitsToBase 16 n)
      where
        toHexDigit k
          | k == 0    = '0'
          | k == 1    = '1'
          | k == 2    = '2'
          | k == 3    = '3'
          | k == 4    = '4'
          | k == 5    = '5'
          | k == 6    = '6'
          | k == 7    = '7'
          | k == 8    = '8'
          | k == 9    = '9'
          | k == 10   = 'a'
          | k == 11   = 'b'
          | k == 12   = 'c'
          | k == 13   = 'd'
          | k == 14   = 'e'
          | otherwise = 'f'
```
