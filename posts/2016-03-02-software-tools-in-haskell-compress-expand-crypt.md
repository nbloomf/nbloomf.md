---
title: Software Tools in Haskell: compress, expand, crypt
author: nbloomf
date: 2016-03-02
---

This post is part of the [Software Tools in Haskell](/posts/2016-02-10-software-tools-in-haskell.html) series.


<a name="compress" />

## ``compress``: compress stdin (run length encoding)

In a list of characters, a *run* is a sublist of characters which are all the same. For example, the list

    bookkeeper

has three runs, each of two characters. If a list contains many long runs, it can be losslessly compressed using a technique called [run length encoding](https://en.wikipedia.org/wiki/Run-length_encoding). With such a scheme, instead of storing a literal run like ``aaaaaaa`` we store the repeated character and the number of times it repeats. Kernighan and Plauger do this by breaking a sequence of characters into two kinds of sublists: *runs*, sublists of repeated characters (longer than some threshold length), and *chunks*, sublists containing no runs. The run length encoding scheme in *Software Tools* then transforms a stream of characters into blocks of the form

    (symbol denoting repeat)
    (character to be repeated)
    (repeat count)

and

    (chunk count)
    (list of that many characters)

Where (symbol denoting repeat) is a special character, which we will call the **sigil**. Let's tweak this scheme just slightly. As K&P point out, no compression scheme can perform well on all input (in fact every compression scheme must make some inputs *bigger*). But we are wise to consider "how bad it gets when it gets bad". How bad does this scheme get? The worst possible input for a run length encoding scheme is one with no runs at all, since there are no opportunities for compression. But notice what happens in this case; the entire input is a "chunk", and so must be encoded with its count. The amount of space required to store an arbitrarily large integer, regardless of the scheme required, is proportional to its number of digits. (We can make that proportion smaller by choosing a larger base, but only to a point.) That means an input stream of length $n$ with no runs will require about $\log(n)$ characters just to store the chunk count, for a "compressed" file size of about $n + \log(n)$. Not great!

What if, instead of keeping track of both chunk sizes and repeat counts, we only keep track of repeat counts and reuse the sigil to also denote the *end* of the repeat count. This way, an encoded stream looks like a stream of

    (sigil)
    (character to be repeated)
    (repeat count)
    (sigil)

and

    (characters not including the sigil)

Of course now we also need to provide a way to encode literal instances of the sigil. What is the simplest way to do this? All characters *other than* the sigil are interpreted literally, unless we want to introduce another escape character. We can't use a single sigil, since that means "start a new encoded run". And we cannot use two sigils, because that means "start a new encoded run of sigils". But three copies of the sigil character in a row does not mean anything, if we remember not to use the sigil character to encode numbers. So we interpret the string

    (sigil)(sigil)(sigil)

to mean a literally encoded sigil. (Note that it is then more space efficient to encode two or more literal sigils as a run. (Two literal sigils is 6 characters in this scheme, but only 4 as a run.))

What is the worst case now? Well, an input stream with no runs *and no sigils* -- a chunk -- will be encoded as is with no overhead. An input stream with no runs and including sigils will require two extra characters for each sigil. In the worst case, a stream of $n$ characters will require about $2n$ characters for the sigils, for a "compressed" size of about $3n$. Really not great!

On the face of it the second scheme is much worse, in the worst case, than the first. But which is worse on realistic data? If we plan to use ``compress`` on textual data we can choose the sigil to be a rarely used character. ASCII includes several control characters, like ``\BEL``, which do not appear in text. Note that if our input does not have any literal sigils, then the second scheme can never compress its input to a larger size as long as we only compress runs of at least 5 characters (as the only way this happens is by encoding literal sigils). On the other hand, the first scheme adds overhead proportional to $\log(n)$ for every chunk of length $n$ -- so unless our input includes long runs, or lots of short runs, the size may not decrease much and can easily increase.

The main program is basic; ``compress`` is a character-oriented filter.


```haskell
-- sth-compress: compress stdin (run length encoding)
--   character-oriented

module Main where

import SoftwareTools.Lib (exitSuccess)
import SoftwareTools.Lib.IO (charFilter)
import SoftwareTools.Lib.Text (rlEncode)

main :: IO ()
main = do
  charFilter (rlEncode '\BEL' 5)
  exitSuccess
```


The actual run length encoding is a little complicated. We define an internal representation for run length encoded data.


```haskell
data RLE a
  = Chunk   [a]
  | Repeat  Int a
  | Literal Int
  deriving Show
```


Doing this is not strictly necessary, but introducing a type for run length encoded data makes it easier to decompose algorithms (algebraic data types are a big win here). Now ``rlEncode`` works in two phases: first it reads a stream of characters into the internal representation of RLEs, and then it serializes that representation as a string.


```haskell
rlEncode :: Char -> Int -> String -> String
rlEncode sig k = showRLE sig . runLengthEncode sig k
  where
    showRLE :: Char -> [RLE Char] -> String
    showRLE sig = concatMap write
      where
        write :: RLE Char -> String
        write (Repeat k x) = concat
          [[sig], [x], showBase86Nat k, [sig]]
        write (Chunk xs) = xs
        write (Literal 1) = [sig,sig,sig]
        write (Literal k) = concat $
          [[sig], [sig], showBase86Nat k, [sig]]

    runLengthEncode :: (Eq a) => a -> Int -> [a] -> [RLE a]
    runLengthEncode sig t = unfoldr (getFirst t) . getRuns
      where
        getFirst _ [] = Nothing
        getFirst t ((x,k):xs)
          | t <= k    = Just (Repeat k x, xs)
          | x == sig  = Just (Literal k, xs)
          | otherwise = let (ys,zs) = split ((x,k):xs)
                        in Just (Chunk $ fromRuns ys, zs)
              where
                split = span (\(z,h) -> t > h && z /= sig)
```


We use two library functions to work with run-encoded lists.


```haskell
getRuns :: (Eq a) => [a] -> [(a, Int)]
getRuns = unfoldr firstRun
  where
    firstRun :: (Eq a) => [a] -> Maybe ((a, Int), [a])
    firstRun []     = Nothing
    firstRun (x:xs) = let (as,bs) = span (== x) xs in
      Just ((x, 1 + count as), bs)

fromRuns :: [(a, Int)] -> [a]
fromRuns = concatMap (\(x,k) -> replicate k x)
```


Repeat counts are encoded in base 86 for space efficiency. (Counts up to 85 need only one character, counts up to 7395 need at most two, and up to 636055 need at most three.)


```haskell
digitsToBase :: Int -> Int -> [Int]
digitsToBase b k
  | b <= 1 || k < 0 = []
  | otherwise = reverse $ foo k
      where
        foo t
          | t < b = [t]
          | otherwise = (t`rem`b) : (foo (t`quot`b))


showBase86Nat :: Int -> String
showBase86Nat k
  | k < 0     = ""
  | otherwise = case sequence $ map intToChar $ digitsToBase 86 k of
      Nothing -> error "showBase86Nat"
      Just x  -> x
      
  where
    intToChar :: Int -> Maybe Char
    intToChar x = lookup x $ map swap
      [ ('0',0),  ('1',1),  ('2',2),  ('3',3),  ('4',4)
      , ('5',5),  ('6',6),  ('7',7),  ('8',8),  ('9',9)
      , ('a',10), ('b',11), ('c',12), ('d',13), ('e',14)
      , ('f',15), ('g',16), ('h',17), ('i',18), ('j',19)
      , ('k',20), ('l',21), ('m',22), ('n',23), ('o',24)
      , ('p',25), ('q',26), ('r',27), ('s',28), ('t',29)
      , ('u',30), ('v',31), ('w',32), ('x',33), ('y',34)
      , ('z',35), ('A',36), ('B',37), ('C',38), ('D',39)
      , ('E',40), ('F',41), ('G',42), ('H',43), ('I',44)
      , ('J',45), ('K',46), ('L',47), ('M',48), ('N',49)
      , ('O',50), ('P',51), ('Q',52), ('R',53), ('S',54)
      , ('T',55), ('U',56), ('V',57), ('W',58), ('X',59)
      , ('Y',60), ('Z',61), ('?',62), ('!',63), ('#',64)
      , ('&',65), ('@',66), ('$',67), ('=',68), ('+',69)
      , ('-',70), ('~',71), ('<',72), ('>',73), ('[',74)
      , (']',75), ('(',76), (')',77), ('{',78), ('}',79)
      , ('|',80), ('/',81), ('*',82), ('^',83), (':',84)
      , (';',85)
      ]

    swap (x,y) = (y,x)
```

It will be difficult to test ``compress`` until we've also written...



<a name="expand" />

## ``expand``: uncompress stdin (run length encoding)

The companion to ``compress`` is ``expand``. It reads a string of characters that was run length encoded by ``compress`` and uncompresses it. This program has an error condition; the input may not be valid. This can happen for a few reasons; if a repeat count is incorrectly encoded (i.e. includes invalid digits or does not terminate in a sigil), or if the file ends in the middle of a repeat encoding.

```haskell
-- sth-expand: uncompress stdin (run length encoding)
--   character-oriented

module Main where

import SoftwareTools.Lib
  (exitSuccess, exitFailure)
import SoftwareTools.Lib.IO (charFilter)
import SoftwareTools.Lib.Text (rlDecode)
import SoftwareTools.Lib.Error (reportErrorMsgs)

main :: IO ()
main = do
  xs <- getContents

  ys <- case rlDecode '\BEL' xs of
          Just zs -> return zs
          Nothing -> reportErrorMsgs
                       [ "corrupt input"
                       ] >> exitFailure

  putStr ys
  exitSuccess
```


``rlDecode`` does all the work:


```haskell
rlDecode :: Char -> String -> Maybe String
rlDecode sig = fmap (runLengthDecode sig) . readRLE sig
  where
    runLengthDecode :: (Eq a) => a -> [RLE a] -> [a]
    runLengthDecode sig = concatMap decodeRLE
      where
        decodeRLE (Chunk  xs)  = xs
        decodeRLE (Repeat k x) = replicate k x
        decodeRLE (Literal k)  = replicate k sig

    readRLE :: Char -> String -> Maybe [RLE Char]
    readRLE sig = unfoldrMaybe readFirstRLE
      where
        readFirstRLE :: String -> Maybe (Maybe (RLE Char, String))
        readFirstRLE ""  = Just Nothing
        readFirstRLE [x] =
          if x == sig then Nothing else Just (Just (Chunk [x], ""))
        readFirstRLE [x,y] =
          if x == sig then Nothing else Just (Just (Chunk [x], [y]))
        readFirstRLE (x:y:z:xs)
          | x == sig && y == sig && z == sig
              = Just (Just (Literal 1, xs))
          | x == sig && y == sig && z /= sig
              = do
                  let (as,bs) = span (/= sig) (z:xs)
                  k <- readBase86Nat as
                  case bs of
                    ""     -> Just (Just (Repeat k y, ""))
                    (_:cs) -> Just (Just (Repeat k y, cs))
          | x == sig && y /= sig
              = do
                  let (as,bs) = span (/= sig) (z:xs)
                  k <- readBase86Nat as
                  case bs of
                    ""     -> Just (Just (Repeat k y, ""))
                    (_:cs) -> Just (Just (Repeat k y, cs))
          | otherwise
              = do
                  let (as,bs) = span (/= sig) (x:y:z:xs)
                  Just (Just (Chunk as, bs))
```


One big improvement we could make to ``expand`` is to try to handle invalid input more gracefully; we could output the partially expanded text, for instance, or tell the user exactly where the error occurs. The first idea would not be too difficult. (Write the output to stderr.) The second idea, though, while possibly useful, would make the implementation much more complicated. (We'd have to keep track of the position of each character in the original source.) Doable, but until the need is demonstrated I'd prefer to keep the implementation simple.


<a name="crypt" />

## ``crypt``: xor stdin with a list of keys

This program performs very simple encryption by xor-ing stdin with a list of keys, supplied by the user at the command line.

At the bit level, ``a xor b`` is 0 if ``a`` and ``b`` are equal and is ``1`` otherwise. Two lists of bits are ``xor``ed entrywise, with the shorter list padded with $0$s. We can think of ``xor`` as an operation on natural numbers by converting to and from base 2, and finally we can think of ``xor`` as an operation on *characters* by converting to and from natural numbers (a.k.a. code points). Then to ``xor`` two strings we ``xor`` characterwise.

We will implement these operations bare-handed.


```haskell
data Bit
  = Zero | One
  deriving (Eq, Show)

intToBits :: (Integral n) => n -> [Bit]
intToBits k = case getBits k of
  [] -> [Zero]
  bs -> bs
  where
    getBits t
      | t <= 0    = []
      | otherwise = case even t of
          True  -> Zero : (getBits $ t`quot`2)
          False -> One  : (getBits $ (t-1)`quot`2)

bitToInt :: (Integral n) => Bit -> n
bitToInt Zero = 0
bitToInt One  = 1

bitsToInt :: (Integral n) => [Bit] -> n
bitsToInt = sum . zipWith (*) [2^t | t <- [0..]] . map bitToInt

bitXOR :: Bit -> Bit -> Bit
bitXOR Zero Zero = Zero
bitXOR Zero One  = One
bitXOR One  Zero = One
bitXOR One  One  = Zero

bitsXOR :: [Bit] -> [Bit] -> [Bit]
bitsXOR [] ys = ys
bitsXOR xs [] = xs
bitsXOR (x:xs) (y:ys)
  = (bitXOR x y) : bitsXOR xs ys

intXOR :: (Integral n) => n -> n -> n
intXOR a b = bitsToInt $ bitsXOR (intToBits a) (intToBits b)
```


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


```haskell
-- sth-crypt: xor stdin with a list of keys
--   character-oriented

module Main where

import SoftwareTools.Lib (getArgs, exitSuccess)
import SoftwareTools.Lib.IO (charFilter)
import SoftwareTools.Lib.Text
  (toCodePoint, fromCodePoint, backslashUnEscape)
import SoftwareTools.Lib.Bit (intXOR)

main :: IO ()
main = do
  keys <- getArgs
  charFilter (cryptKeys (map backslashUnEscape keys))
  exitSuccess


cryptKeys :: [String] -> String -> String
cryptKeys []     str = str
cryptKeys (k:ks) str = cryptKeys ks (crypt k str)

crypt :: String -> String -> String
crypt ""  str  = str
crypt key str = zipWith xorChar str (concat $ repeat key)
  where
    xorChar :: Char -> Char -> Char
    xorChar x y
      = fromCodePoint $ intXOR (toCodePoint x) (toCodePoint y)
```


Some notes: ``toCodePoint`` and ``fromCodePoint`` are synonyms for standard library functions which (surprise!) convert characters to and from their unicode code points.

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
