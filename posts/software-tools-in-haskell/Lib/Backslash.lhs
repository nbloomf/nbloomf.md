---
title: "Software Tools in Haskell: Escape Codes"
date: 2016-02-20
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-unescape: interpret C and ASCII backslash escape codes on stdin
> module Lib.Backslash (bsUnEsc) where
> 
> import Data.List (unfoldr)
> import Data.Char (ord, readLitChar)

In several tools to come we will need a function which expands escape codes in a string. This module provides just such a function, called ``bsUnEsc``.

There's no nice way to do this, so we pattern match on the prefix of a string looking for escape codes. One gotcha: the ASCII abbreviations are not [prefix free](https://en.wikipedia.org/wiki/Prefix_code); for instance the meaning of the string ``\SOHello`` is ambiguous; is it ``\SO`` (Shift Out) followed by ``Hello`` or ``\SOH`` (Start Of Heading) followed by ``ello``? To make sure these are detected correctly, we pattern match ``\SOH`` first (since otherwise that string would always match as ``\SO`` followed by ``H``) and add one more escape code, ``\&`` (taken from Haskell), for those occasions when you *really* want ``\SO`` followed by ``H`` not interpreted as ``\SOH``. ``\&`` represents the empty string, so we can do this with ``\SO\&H``. So, you know, for all those times you need carefully formatted ASCII control codes.

``bsUnEsc`` is the bulk of the [unescape](/posts/software-tools-in-haskell/unescape.html) tool, but it will be useful in several other tools as well. So we extract it in a library.

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
