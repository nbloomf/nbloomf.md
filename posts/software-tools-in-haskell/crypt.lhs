---
title: Software Tools in Haskell: crypt
subtitle: xor stdin with a list of keys
date: 2016-02-25
author: nbloomf
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-crypt: xor chars on stdin with a list of keys
> module Main where
> 
> import System.Environment (getArgs)
> import System.Exit (exitSuccess)
> import Data.Char (ord, chr, readLitChar)
> import Data.List (unfoldr)

This program performs very (very!) simple encryption by xor-ing ``stdin`` with a list of keys, supplied by the user at the command line.

At the bit level, ``a xor b`` is 0 if ``a`` and ``b`` are equal and is ``1`` otherwise. Two lists of bits are ``xor``ed entrywise, with the shorter list padded with $0$s. We can think of ``xor`` as an operation on natural numbers by converting to and from base 2, and finally we can think of ``xor`` as an operation on *characters* by converting to and from natural numbers (a.k.a. code points). Then to ``xor`` two strings we ``xor`` characterwise.

We will implement these operations bare-handed.

> class XOR t where
>   xor :: t -> t -> t
> 
>   xors :: [t] -> [t] -> [t]
>   xors [] ys = ys
>   xors xs [] = xs
>   xors (x:xs) (y:ys) = (xor x y) : xors xs ys
> 
> 
> data Bit
>   = Zero | One
>   deriving (Eq, Show)
> 
> instance XOR Bit where
>   xor Zero Zero = Zero
>   xor Zero One  = One
>   xor One  Zero = One
>   xor One  One  = Zero
> 
> 
> instance XOR Int where
>   xor a b = bitsToInt $ xors (intToBits a) (intToBits b)
>     where
>       intToBits :: (Integral n) => n -> [Bit]
>       intToBits k = case getBits k of
>         [] -> [Zero]
>         bs -> bs
>         where
>           getBits t
>             | t <= 0    = []
>             | otherwise = case even t of
>                 True  -> Zero : (getBits $ t`quot`2)
>                 False -> One  : (getBits $ (t-1)`quot`2)
> 
>       bitsToInt :: (Integral n) => [Bit] -> n
>       bitsToInt = sum . zipWith (*) [2^t | t <- [0..]] . map bitToInt
>         where
>           bitToInt Zero = 0
>           bitToInt One  = 1
> 
> 
> instance XOR Char where
>   xor x y = chr $ xor (ord x) (ord y)

When we ``xor`` two strings together, one is called the *plaintext* and the other is called the *key*. If the key is shorter than the plaintext we simply repeat it from the beginning as many times as needed. The result is a new string, the *ciphertext*, which will generally not be recognizable. However, we can recover the plaintext by repeating the ``xor`` operation with the same key.

This method of encrytion has several interesting properties. (I am hesitant to call these unequivocal "pros" or "cons", since every encryption scheme involves tradeoffs.)

* Extremely simple to implement.
* Is a symmetric cipher; in fact, exactly the same key is used for encryption and decryption.
* If the key is short compared to the text, is vulnerable to statistical attacks. (Beyond the usual brute-force attacks that come with short keys.)
* Can be used to implement a [one-time pad](https://www.wikipedia.org/wiki/One-time_pad), which to my knowledge is the only provably secure encryption scheme. (To do this, the key must be the same length as the plaintext.)
* Can only be used on character encodings of size $2^n$ (which unicode is), which preferably have a canonical mapping to the integers from $0$ to $2^n - 1$ (which unicode does).
* When used on a large alphabet, most significant bits can play an important role. For instance, if we are encrypting a text which consists only of ASCII (the first 128 characters of unicode) and use a key consisting of characters with a bit higher than the 7th set, then these high bits will never be ``xor``ed away. I haven't thought about this in depth, but I suspect this opens up a new class of statistical attacks.
* Related to the previous property, practical text does not use the full range of unicode -- more likely it is restricted to the characters used in a particular language. This may open a class of attacks.
* When used with ASCII or unicode, generally the ciphertext will include control characters. This can make it inconvenient to use text-oriented tools on encrypted text. We could fix this with a different mapping from characters to numbers, but doing so would probably weaken the encryption even further by reducing the alphabet size.

Here's the main program.

> main :: IO ()
> main = do
>   keys <- fmap (map bsUnEsc) getArgs
>   charFilter (cryptWith keys)
>   exitSuccess
> 
> 
> cryptWith :: [String] -> String -> String
> cryptWith ks str = foldr crypt str ks
>   where
>     crypt :: String -> String -> String
>     crypt ""  str = str
>     crypt key str = zipWith xor str (concat $ repeat key)

We definitely want the user to specify an encryption key from the command line. But generally, the user can specify many (or no!) command line arguments. What should we do if that happens?

* If the user does not specify a key, then the simplest thing to do is return the plaintext unchanged. We could return an error, but it is feasible that some future user would prefer that "no key" be treated the same as "empty key". Moreover, the recursive definition of ``cryptKeys`` is much cleaner with this decision.
* We could just silently ignore any arguments after the first, but then the presence of extra arguments likely signifies that the user misunderstands how to use the program.
* We could simply concatenate the arguments together as a single larget key.
* We could interpret the command line arguments as a *list* of keys, and use all of them, one at a time.

Concatenating the arguments to a single key would be fine. But interpreting the arguments as multiple keys, to be used independently, has a nice side effect. It provides a simple (if not maximally secure) way for the user to increase the effective size of the key. As K&P note, if we ``xor`` encrypt a given file twice with two different keys, of lengths $m$ and $n$, then this is equivalent to ``xor``ing once with a single key of length $\mathrm{lcm}(m,n)$. For instance,

    crypt "foo" "quuux"

with two keys of length 3 and 5, is equivalent to running ``crypt`` with a key of length 15. Saying

    crypt "foo" "quuux" "mungely"

is just like using a key of length 105.

The keys are also run through ``backslashUnEscape`` by default, meaning that any C or ASCII style escape codes are interpreted. This is the Right Thing because we want the user to have easy access to the widest possible range of keys. It is not necessary to clutter the interface by making this functionality optional with an extra command line argument.

I can think of one important possible improvement to ``crypt``: it would be nice if we could specify the keys as files as well as arguments. For instance, an invocation like

    crypt "foo" "quuux" --keyfiles key1.txt key2.txt

would treat the contents of ``key1.txt`` and ``key2.txt`` as keys, just like ``foo`` and ``quuux``. We generally do not want to leave encryption keys lying around in files. But this would make it easier to use very large keys, for instance to implement a one-time pad. That's an idea for another day.


Old stuff
---------

> -- apply a map to stdin
> charFilter :: (String -> String) -> IO ()
> charFilter f = do
>   xs <- getContents
>   putStr $ f xs
> 
> 
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

woo
