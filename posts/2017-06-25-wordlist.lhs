---
title: Wordlist
author: nbloomf
date: 2017-06-25
tags: literate-haskell
---

> {-# LANGUAGE BangPatterns         #-}
> {-# LANGUAGE TypeSynonymInstances #-}
> {-# LANGUAGE FlexibleInstances    #-}
> module Main where
> 
> import Control.Monad
> import Control.Monad.Writer
> import System.FilePath
> import System.Exit
> import System.Environment
> import Data.List
> import Data.List.Split
> import Text.ParserCombinators.Parsec

For a project I'm fiddling with (to be written up at some point) I found myself wishing I had a machine-readable dictionary of English words, including parts of speech, pronunciations, and division into syllables. As I'm sure we all do from time to time. :) It doesn't need to be fancy -- just a tab delimited file with lines like

    word   part_of_speech   IPA_pronunciation   syllables

for as many English words as I can get. Fortunately for me, there are several large databases of this sort available under open licenses. I was able to find these:

1. The [Moby Project](https://en.wikipedia.org/wiki/Moby_Project) (public domain) by Grady Ward -- a huge trove of data and the only reason I thought this project would be feasible. Can be downloaded from [Project Gutenberg](http://www.gutenberg.org/ebooks/author/1132?sort_order=title).
2. The English [Wiktionary](https://en.wiktionary.org) (CC-BY-SA/GFDL) -- also a huge trove of pronunciations and parts of speech, but less structured than the Moby Project. Wiktionary makes database dumps available for download; I used the one from [June 20, 2017](https://dumps.wikimedia.org/enwiktionary/20170620/), but by the time you are reading this a more recent version will be up.
3. The [Google Books Ngrams Viewer](http://storage.googleapis.com/books/ngrams/books/datasetsv2.html) data (CC-BY-3.0) -- specifically, the unigrams. This is more useful for the frequency data (to be used later) but also includes some part of speech data. Warning: these files are enormous.
4. The [WordNet](https://wordnet.princeton.edu/) project (idiosyncratic license, but seems to be permissive). Focused more on semantic relations among words, still a great resource.
5. The [GCIDE](http://www.ibiblio.org/webster/), a.k.a. GNU Collaborative International Dictionary of English (GPL3, not surprisingly) -- based on the public domain Webster's Unabridged 1913 and supplemented with WordNet.

There are probably other sources out there too, but this is a good start.

To give away the punchline, the final database is available on [GitHub](https://github.com/nbloomf/wordlist). This post is an explanation of the scripts I used to generate that file.

Clearly editing by hand is a non-starter. Instead we'll build some small tools to parse our open dictionary data and merge it together the best we can manage. I will focus my attention on the Moby project and Wiktionary for now, since the other resources seem to be focused on kinds of data I'm less interested in for this project.

I'll begin with the Moby Project data, since it explicitly contains everything I want -- part of speech, pronunciation, and hyphenation (which a spot check indicates is a decent proxy for syllables). The first problem is that the Moby Project data isn't encoded as UTF-8 text. This is reasonable, since unicode barely existed when the Moby Project was put in the public domain. Wikipedia indicates that it is encoded as "macintosh roman" text, which we can test with

```bash
cat foo.txt | iconv -f macintosh -t utf-8 > foo-utf8.txt
```

replacing ``foo`` with whatever file needs to be converted. (I know this is a [Useless Use of Cat](http://porkmail.org/era/unix/award.html) and I don't care; having data flow in one direction makes more sense to me.) The line endings are also ``CRLF``-style, which can be fixed with ``sed`` or (as I did) a text editor. Fixing up the encoding and line endings of the Moby files, I ended up with the following:

1. ``mwords.txt``: 354984 lines.
2. ``mhyph.txt``: 187175 lines, with hyphenation points (other than spaces or hyphens that are part of the word) indicated by a "•" symbol.
3. ``mpos.txt``: 233356 lines, with part(s) of speech given by a particular encoding scheme.
4. ``mpron.txt``: 177267 lines, with IPA pronunciation using an ASCII encoding.

In other words, jackpot. The data I want is there. It is, however, encoded, so we'll have to do some tinkering to get it in the format I want. For example, a typical line in ``mhyph.txt`` looks like this:

    so•da foun•tain

while a typical line in ``mpos.txt`` looks like this:

    double-time\ti

and a typical line in ``mpron.txt`` looks like this:

    flibbertigibbet 'fl/I/b/@/rt/i/,/dZ//I/b/I/t

Unifying all this will be a little more complicated and error-prone than my ``awk`` skills can handle, so I'll use Haskell instead. This may turn out to be overkill, but we'll see.

My strategy will be something like this.

* First, define types for the data we eventually want to store in a database -- namely, ``Word``s.
* Write functions for rendering and parsing ``Word``s in the format I want to use in the final database.
* Write functions to parse ``Word``s from the textual formats in our open sources -- the Moby files, and Wiktionary, and Google Ngrams.
* Finally, actually parse the data, merge it, and write it to a single flatfile database.

Let's get to it!


Basic Types
===========

About this database. Each record needs to represent a "word". But what is a "word", exactly? I'm not a linguist and am too lazy to look this up, but to my eye a word has the following things.

1. A *written* representation (how you write it),
2. A *spoken* representation (how you say it),
3. A *grammatical function* (how you use it), and
4. A *meaning*.

If two "words" are such that any of these items differ, then the words are different. For instance "close" (verb) and "close" (adjective) are spelled the same, but have different functions and pronunciations, so are different words. Likewise "run" (move by flapping your legs) and "run" (execute a computer program) are different words, despite being spelled and spoken the same way and both being nouns.

Of course real language is not so clear cut. For instance, the written and spoken representations of a word don't have to be unique (think US vs. UK spellings, or accents). But for my needs this is good enough. (I have to remember, this is for a specific project!)

I will represent words using the following sum type. Note in particular that ``part_of_speech``, ``pronunciation``, and ``syllables`` are all ``Maybe``s, while ``spelling`` is not, and a word can have at most one pronunciation. These choices privilege written words and "General American" pronunciations, but I'm ok with that for now.

> data Word = Word
>   { spelling       :: String
>   , part_of_speech :: Maybe PartOfSpeech
>   , pronunciation  :: Maybe Pronunciation
>   , hyphenation    :: Maybe Hyphenation
>   } deriving Show

And a simple constructor:

> word :: String -> Word
> word x = Word
>   { spelling       = x
>   , part_of_speech = Nothing
>   , pronunciation  = Nothing
>   , hyphenation    = Nothing
>   }

Eventually we will want to store lists of words in text files. I'll wrap functions to write and parse ``Word``s behind the class ``DictFormat``. Since parsing can fail, it will return a ``Writer [String] t``rather than simply ``t``; the ``[String]`` type is meant for logging error messages.

> class DictFormat t where
>   writeDictFormat :: t -> String
>   readDictFormat  :: String -> Writer [String] t

For example:

> instance DictFormat String where
>   writeDictFormat = id
>   readDictFormat  = return
> 
> instance (DictFormat t) => DictFormat (Maybe t) where
>   writeDictFormat Nothing  = ""
>   writeDictFormat (Just x) = writeDictFormat x
> 
>   readDictFormat "" = return Nothing
>   readDictFormat cs = do
>     x <- readDictFormat cs
>     return x

And assuming ``DictFormat`` instances exist for ``PartOfSpeech``, ``Pronunciation``, and ``Hyphenation``, we can define:

> instance DictFormat Word where
>   writeDictFormat w = intercalate "\t"
>     [ writeDictFormat $ spelling w
>     , writeDictFormat $ part_of_speech w
>     , writeDictFormat $ pronunciation w
>     , writeDictFormat $ hyphenation w
>     ]
> 
>   readDictFormat cs = case wordsBy (== '\t') cs of
>     [a,b,c,d] -> do
>       sp  <- readDictFormat a
>       pos <- readDictFormat b
>       pro <- readDictFormat c
>       hyp <- readDictFormat d
>       return $ Word
>         { spelling = sp
>         , part_of_speech = pos
>         , pronunciation  = pro
>         , hyphenation    = hyp
>         }
>     _ -> do
>       tell $ ["Unrecognized format: " ++ cs]
>       return $ word "error"

Now for the summand types. ``PartOfSpeech`` is (for now) determined by the possible values in the Moby data.

> data PartOfSpeech
>   = Noun
>   | NounSingular
>   | NounPlural
>   | NounPhrase
>   | Verb
>   | VerbParticiple
>   | VerbTransitive
>   | VerbIntransitive
>   | Adjective
>   | Adverb
>   | Conjunction
>   | Preposition
>   | Interjection
>   | Pronoun
>   | ArticleDefinite
>   | ArticleIndefinite
>   | Nominative
>   | Unknown
>   deriving (Eq, Ord, Show)

For now we'll use an ad-hoc ``DictFormat`` encoding of this type.

> instance DictFormat PartOfSpeech where
>   writeDictFormat x = case x of
>     Noun              -> "n"
>     NounSingular      -> "n-s"
>     NounPlural        -> "n-pl"
>     NounPhrase        -> "n-ph"
>     Verb              -> "v"
>     VerbParticiple    -> "v-p"
>     VerbTransitive    -> "v-t"
>     VerbIntransitive  -> "v-i"
>     Adjective         -> "adj"
>     Adverb            -> "adv"
>     Conjunction       -> "conj"
>     Preposition       -> "pre"
>     Interjection      -> "int"
>     Pronoun           -> "pro"
>     ArticleDefinite   -> "a-def"
>     ArticleIndefinite -> "a-ind"
>     Nominative        -> "nom"
>     Unknown           -> ""
> 
>   readDictFormat cs = case cs of
>     "n"     -> return Noun
>     "n-s"   -> return NounSingular
>     "n-pl"  -> return NounPlural
>     "n-ph"  -> return NounPhrase
>     "v"     -> return Verb
>     "v-p"   -> return VerbParticiple
>     "v-t"   -> return VerbTransitive
>     "v-i"   -> return VerbIntransitive
>     "adj"   -> return Adjective
>     "adv"   -> return Adverb
>     "conj"  -> return Conjunction
>     "pre"   -> return Preposition
>     "int"   -> return Interjection
>     "pro"   -> return Pronoun
>     "a-def" -> return ArticleDefinite
>     "a-ind" -> return ArticleIndefinite
>     "nom"   -> return Nominative
>     _ -> do
>       tell ["Unrecognized part of speech: " ++ cs]
>       return Unknown

Pronunciations will eventually be strings of IPA characters, but the Moby data uses an ASCII encoding of IPA. We'll just store these as strings, without doing any kind of validation.

> data Pronunciation = Pron
>   { unPron :: String
>   } deriving (Eq, Show)
> 
> instance DictFormat Pronunciation where
>   writeDictFormat = unPron
> 
>   readDictFormat cs = return $ Pron { unPron = cs }

``Hyphenation`` is a little trickier. In the Moby database, syllables of a given word are delimited by any of three different characters. Compound words have their parts separated by spaces, hyphenated words are divided by hyphens (of course), and the possible hyphenation points of a simple word are separated by bullets. These form a kind of hierarchy which we can model by saying that a "word" is a list of lists of lists of syllables, with the outer list delimited by spaces and the middle lists delimited by hyphens.

> data Hyphenation = Hyp
>   { unHyp :: [[[String]]]
>   } deriving (Eq, Show)

This is a decent format for storing hyphenations, so I'll steal it for our eventual final database.

> instance DictFormat Hyphenation where
>   writeDictFormat =
>       intercalate " "
>     . map (intercalate "-")
>     . map (map (intercalate "•"))
>     . unHyp
> 
>   readDictFormat =
>       return
>     . Hyp
>     . map (map (wordsBy (== '•')))
>     . map (wordsBy (== '-'))
>     . wordsBy (== ' ')


Parsing Moby Data
=================

Next we'll deal with parsing the Moby files. For reasons we'll see in a moment, instead of parsing the files as lists of ``Word``s, we'll simply parse them as key-value pairs, keyed by the spelling of the word. For instance, the hyphenation file will become a ``[(String, Hyphenation)]``. First we need a helper function to strip extra spaces from a string.

> stripSpaces :: String -> String
> stripSpaces =
>     reverse
>   . dropWhile (== ' ')
>   . reverse
>   . dropWhile (== ' ')

Parsing the list of words alone is simple enough.

> readWords :: FilePath -> IO [(String,())]
> readWords path = do
>   raw <- fmap (map stripSpaces . lines) $ readFile path
>   return $ map (\x -> (x, ())) raw

Parsing in the Moby hyphenations list is also not too bad; we just need to filter out the bullet characters to recover the original word.

> readMobyHyph :: FilePath -> IO [(String, Hyphenation)]
> readMobyHyph path = do
>   let
>     parseRecord :: String -> (String, Hyphenation)
>     parseRecord str =
>       ( stripSpaces $ filter (/= '•') str
>       , let (x,_) = runWriter $ readDictFormat str in x
>       )
> 
>   raw <- fmap lines $ readFile path
>   return $ map parseRecord raw

Parsing the part of speech file is a little trickier; each word can have several parts of speech, and the part of speech codes may be "invalid". (I found a couple of POS codes that made no sense!)

Part of speech information is stored in the Moby files using two different formats: one in the part of speech file, and another in the pronunciation file. We'll define two functions for parsing both kinds.

> mobyPOSCode :: Char -> Either String PartOfSpeech
> mobyPOSCode c = case c of
>   'N' -> Right NounSingular
>   'p' -> Right NounPlural
>   'h' -> Right NounPhrase
>   'V' -> Right VerbParticiple
>   't' -> Right VerbTransitive
>   'i' -> Right VerbIntransitive
>   'A' -> Right Adjective
>   'v' -> Right Adverb
>   'C' -> Right Conjunction
>   'P' -> Right Preposition
>   '!' -> Right Interjection
>   'r' -> Right Pronoun
>   'D' -> Right ArticleDefinite
>   'I' -> Right ArticleIndefinite
>   'o' -> Right Nominative
>   _   -> Left $ "Unknown part of speech: " ++ [c]

Parsing the actual file:

> readMobyPOS :: FilePath -> IO [(String, PartOfSpeech)]
> readMobyPOS path = do
>   let
>     makeWord :: String -> Char -> Writer [String] [(String, PartOfSpeech)]
>     makeWord !word code =
>       case mobyPOSCode code of
>         Left msg -> do
>           tell [msg]
>           return []
>         Right pos -> do
>           return [( stripSpaces word, pos )]
> 
>     parseRecord :: String -> Writer [String] [(String, PartOfSpeech)]
>     parseRecord !str = do
>       let (pos,drow) = break (== '\\') $ reverse str
> 
>       case drow of
>         '\\':x ->
>           fmap concat $ sequence $ map (makeWord $ reverse x) pos
>
>         _ -> do
>           tell ["Unexpected format: " ++ reverse drow]
>           return []
> 
>   raw <- fmap lines $ readFile path
>   let (dict,err) = runWriter $ fmap concat $ sequence $ map parseRecord raw
>   
>   case err of
>     [] -> return ()
>     _  -> do
>       putStrLn $ "parse errors in " ++ path
>       sequence_ $ map putStrLn err
>       exitFailure
> 
>   return dict

Parsing pronunciations is also tricky. Some words have more than one pronunciation, depending on their part of speech. First a helper to parse part of speech codes.

> mobyPronPOSCode :: String -> Either String PartOfSpeech
> mobyPronPOSCode s = case s of
>   "n"   -> Right Noun
>   "v"   -> Right Verb
>   "aj"  -> Right Adjective
>   "av"  -> Right Adverb
>   "inj" -> Right Interjection
>   "prp" -> Right Preposition
>   _     -> Left $ "Unknown part of speech: " ++ s

The pronunciations themselves are not stored using IPA, but rather a kind of ASCII encoding. The following helper function is my best attempt at converting one to the other. :) I had to correct some errors in the data by hand.

> mobyToIPA :: String -> Writer [String] String
> mobyToIPA str = case str of
>   []               -> return []
>   ('(':'/':'@':'/':')':cs) -> fmap ('ə':) $ mobyToIPA cs
>   ('e':'/':'T':'/':cs)     -> fmap ("ɛð" ++) $ mobyToIPA cs
>   ('/' :cs)        -> mobyToIPA cs
>   ('\'':cs)        -> fmap ('\'':)   $ mobyToIPA cs
>   (',' :cs)        -> fmap (',':)    $ mobyToIPA cs
>   ('_' :cs)        -> fmap ('#':)    $ mobyToIPA cs
>   ('.' :cs)        -> fmap ('.':)    $ mobyToIPA cs
>   (' ' :cs)        -> fmap ('.':)    $ mobyToIPA cs
>   ('[':'@':']':cs) -> fmap ('ɝ':)    $ mobyToIPA cs
>   ('(':'@':')':cs) -> fmap ("ɛə" ++) $ mobyToIPA cs
>   ('t':'S':cs)     -> fmap ("tʃ" ++) $ mobyToIPA cs
>   ('@':'r':cs)     -> fmap ("ɜr" ++) $ mobyToIPA cs
>   ('a':'I':cs)     -> fmap ("aɪ" ++) $ mobyToIPA cs
>   ('A':'r':cs)     -> fmap ("ɑr" ++) $ mobyToIPA cs
>   ('A':'U':cs)     -> fmap ("aʊ" ++) $ mobyToIPA cs
>   ('d':'Z':cs)     -> fmap ("dʒ" ++) $ mobyToIPA cs
>   ('e':'I':cs)     -> fmap ("eɪ" ++) $ mobyToIPA cs
>   ('h':'w':cs)     -> fmap ("hw" ++) $ mobyToIPA cs
>   ('O':'i':cs)     -> fmap ("ɔɪ" ++) $ mobyToIPA cs
>   ('o':'U':cs)     -> fmap ("oʊ" ++) $ mobyToIPA cs
>   ('o':'u':cs)     -> fmap ("aʊ" ++) $ mobyToIPA cs
>   ('e':'R':cs)     -> fmap ("ɛʁ" ++) $ mobyToIPA cs
>   ('0':'0':cs)     -> fmap ("u" ++)  $ mobyToIPA cs
>   ('æ':cs)         -> fmap ("æ" ++)  $ mobyToIPA cs
>   ('&':cs)         -> fmap ("æ" ++)  $ mobyToIPA cs
>   ('a':cs)         -> fmap ("æ" ++)  $ mobyToIPA cs
>   ('-':cs)         -> fmap ("ə" ++)  $ mobyToIPA cs
>   ('@':cs)         -> fmap ("ʌ" ++)  $ mobyToIPA cs
>   ('A':cs)         -> fmap ("ɑː" ++) $ mobyToIPA cs
>   ('b':cs)         -> fmap ("b" ++)  $ mobyToIPA cs
>   ('c':cs)         -> fmap ("k" ++)  $ mobyToIPA cs
>   ('d':cs)         -> fmap ("d" ++)  $ mobyToIPA cs
>   ('D':cs)         -> fmap ("ð" ++)  $ mobyToIPA cs
>   ('E':cs)         -> fmap ("ɛ" ++)  $ mobyToIPA cs
>   ('e':cs)         -> fmap ("ɛ" ++)  $ mobyToIPA cs
>   ('f':cs)         -> fmap ("f" ++)  $ mobyToIPA cs
>   ('g':cs)         -> fmap ("ɡ" ++)  $ mobyToIPA cs
>   ('h':cs)         -> fmap ("h" ++)  $ mobyToIPA cs
>   ('i':cs)         -> fmap ("iː" ++) $ mobyToIPA cs
>   ('I':cs)         -> fmap ("ɪ" ++)  $ mobyToIPA cs
>   ('j':cs)         -> fmap ("j" ++)  $ mobyToIPA cs
>   ('k':cs)         -> fmap ("k" ++)  $ mobyToIPA cs
>   ('l':cs)         -> fmap ("l" ++)  $ mobyToIPA cs
>   ('m':cs)         -> fmap ("m" ++)  $ mobyToIPA cs
>   ('n':cs)         -> fmap ("n" ++)  $ mobyToIPA cs
>   ('N':cs)         -> fmap ("ŋ" ++)  $ mobyToIPA cs
>   ('O':cs)         -> fmap ("ɔː" ++) $ mobyToIPA cs
>   ('o':cs)         -> fmap ("ɑ" ++)  $ mobyToIPA cs
>   ('p':cs)         -> fmap ("p" ++)  $ mobyToIPA cs
>   ('r':cs)         -> fmap ("r" ++)  $ mobyToIPA cs
>   ('s':cs)         -> fmap ("s" ++)  $ mobyToIPA cs
>   ('S':cs)         -> fmap ("ʃ" ++)  $ mobyToIPA cs
>   ('t':cs)         -> fmap ("t" ++)  $ mobyToIPA cs
>   ('T':cs)         -> fmap ("θ" ++)  $ mobyToIPA cs
>   ('u':cs)         -> fmap ("uː" ++) $ mobyToIPA cs
>   ('U':cs)         -> fmap ("ʊ" ++)  $ mobyToIPA cs
>   ('v':cs)         -> fmap ("v" ++)  $ mobyToIPA cs
>   ('V':cs)         -> fmap ("ʋ" ++)  $ mobyToIPA cs
>   ('w':cs)         -> fmap ("w" ++)  $ mobyToIPA cs
>   ('z':cs)         -> fmap ("z" ++)  $ mobyToIPA cs
>   ('Z':cs)         -> fmap ("ʒ" ++)  $ mobyToIPA cs
>   ('R':cs)         -> fmap ("ɹ" ++)  $ mobyToIPA cs
>   ('y':cs)         -> fmap ("ɜː" ++) $ mobyToIPA cs
>   ('x':cs)         -> fmap ("x" ++)  $ mobyToIPA cs
>   ('W':cs)         -> fmap ("w" ++)  $ mobyToIPA cs
>   ('Y':cs)         -> fmap ("uː" ++) $ mobyToIPA cs
>   ('3':cs)         -> fmap ("ɝ" ++)  $ mobyToIPA cs
>   _ -> do
>     tell $ ["Unidentified phoneme: " ++ str]
>     return str

Finally, the function that reads the pronunciation file.

> readMobyPron :: FilePath -> IO [((String, Maybe PartOfSpeech), Pronunciation)]
> readMobyPron path = do
>   let
>     fixSpaces :: Char -> Char
>     fixSpaces '_' = ' '
>     fixSpaces c   = c
> 
>     makeWord !word code !pron =
>       if code == ""
>         then return $ return $
>           ( ( stripSpaces $ map fixSpaces word, Nothing )
>           , Pron pron
>           )
>         else case mobyPronPOSCode code of
>           Left err -> do
>             tell [err]
>             return []
>           Right pos -> return $ return $
>             ( ( stripSpaces $ map fixSpaces word, Just pos )
>             , Pron pron
>             )
> 
>     parseRecord str = do
>       let
>         (stem,pron) = break (== ' ') str
>         (word,pos)  = break (== '/') stem
> 
>       ipa <- mobyToIPA (tail pron)
> 
>       makeWord word (delete '/' pos) ipa
> 
>   raw <- fmap lines $ readFile path
>   let (dict,err) = runWriter $ fmap concat $ sequence $ map parseRecord raw
> 
>   case err of
>     [] -> return ()
>     _  -> do
>       putStrLn $ "parse errors in " ++ path
>       sequence_ $ map putStrLn err
>       exitFailure
> 
>   return dict

woo


Merging
=======

Now that we can parse the Moby data to Haskell types, the big remaining question is how to merge all this data together. After trying a lot of dead ends I've settled on having a single, generic, ``merge`` function that takes a list of ``Word``s and a list of "key-value" pairs, and attempts to update the ``Word``s with the given data, or create new ``Word``s if a given "key" does not exist, or report an error message if it can't figure out what to do. This approach has the benefit that it does not depend on the source of our data, so eventually we can use it to merge in information from other sources.

A couple of caveats about the following function: we must have that if ``order x (keyOf y) == EQ``, then ``match x y == True``. ``mergeIO`` will error out if it ever detects that this constraint does not hold.

> mergeIO
>   -- Error log
>   :: FilePath
>   -- Extract the key of a word
>   -> (Word -> key)
>   -- Render a key
>   -> (key -> String)
>   -- Compare two keys
>   -> (key -> key -> Ordering)
>   -- Check whether a key matches a Word
>   -> (key -> Word -> Bool)
>   -- Update a Word with given key-value pair
>   -> (Word -> (key,val) -> Writer [String] Word)
>   -- Create a new word from a key-value pair
>   -> (key -> val -> Word)
>   -- Update data
>   -> [(key,val)]
>   -- Dictionary
>   -> [Word]
>   -- Updated dictionary
>   -> IO [Word]
> 
> mergeIO errF keyOf print order match fiddle create keyval dict =
>   merge
>     (sortBy (\x y -> order (fst x)   (fst y)  ) keyval)
>     (sortBy (\x y -> order (keyOf x) (keyOf y)) dict)
>   where
>     merge [] bs = return bs
>     merge as [] = return $ map (uncurry create) as
>     merge us@((k,v):as) (b:bs) =
>       case span (\(t,_) -> match t b) us of
>         ([],vs) -> case order k (keyOf b) of
>           LT -> do
>             let w = create k v
>             ws <- merge as (b:bs)
>             return (w:ws)
>           GT -> do
>             ws <- merge ((k,v):as) bs
>             return (b:ws)
>           EQ -> error $ intercalate " "
>             [ "shouldn't happen!"
>             , print k
>             , print (keyOf b)
>             ]
> 
>         (ks,vs) -> do
>           let (xs,ys) = span (\c -> match k c) bs
>           let (zs,errs) = runWriter $ sequence $ map (\m -> foldM fiddle m ks) (b:xs)
>           appendFile errF $ unlines errs
>           ws <- merge vs ys
>           return (zs ++ ws)

By feeding ``mergeIO`` appropriate parameters, we recover specific "merge" functions for different kinds of data. For instance, ``mergeStem`` simply adds new words without any extra data.

> mergeStem
>   :: FilePath -> [(String, ())] -> [Word] -> IO [Word]
> mergeStem errF = mergeIO errF spelling id compare match fiddle create
>   where
>     match :: String -> Word -> Bool
>     match stem w = stem == spelling w
> 
>     fiddle w _ = return w
> 
>     create :: String -> () -> Word
>     create stem _ = word stem

Next a helper to add a part of speech to a ``Word``:

> addPOS :: Word -> (String, PartOfSpeech) -> Writer [String] Word
> addPOS w (stem,pos) = if stem /= spelling w
>   then return w
>   else
>     case part_of_speech w of
>       Nothing ->
>         return $ w { part_of_speech = Just pos }
>       Just q -> do
>         if q == pos
>           then return ()
>           else tell $ return $ intercalate "\t"
>             ["Part of Speech"
>             , "stem: \"" ++ stem ++ "\""
>             , "new: \"" ++ writeDictFormat pos ++ "\""
>             , "old: \"" ++ writeDictFormat q ++ "\""
>             ]
>         return w

And with it, ``mergePOS`` can add a list of parts of speech into a dictionary.

> mergePOS
>   :: FilePath -> [(String, PartOfSpeech)] -> [Word] -> IO [Word]
> mergePOS errF = mergeIO errF spelling id compare match addPOS create
>   where
>     match :: String -> Word -> Bool
>     match stem w = stem == spelling w
> 
>     create :: String -> PartOfSpeech -> Word
>     create stem pos = Word
>       { spelling       = stem
>       , part_of_speech = Just pos
>       , pronunciation  = Nothing
>       , hyphenation    = Nothing
>       }

And a helper to add a hyphenation to a ``Word``:

> addHyph :: Word -> (String, Hyphenation) -> Writer [String] Word
> addHyph w (stem,syl) = if stem /= spelling w
>   then return w
>   else
>     case hyphenation w of
>       Nothing ->
>         return $ w { hyphenation = Just syl }
>       Just q -> do
>         if q == syl
>           then return ()
>           else tell $ return $ intercalate "\t"
>             [ "Hyphenation"
>             , "stem: \"" ++ stem ++ "\""
>             , "new: \"" ++ writeDictFormat syl ++ "\""
>             , "old: \"" ++ writeDictFormat q ++ "\""
>             ]
>         return w

And then ``mergeHyph`` can add a list of hyphenations into a dictionary.

> mergeHyph
>   :: FilePath -> [(String, Hyphenation)] -> [Word] -> IO [Word]
> mergeHyph errF = mergeIO errF spelling id compare match addHyph create
>   where
>     match :: String -> Word -> Bool
>     match stem w = stem == spelling w
> 
>     create :: String -> Hyphenation -> Word
>     create stem syl = Word
>       { spelling       = stem
>       , part_of_speech = Nothing
>       , pronunciation  = Nothing
>       , hyphenation    = Just syl
>       }

Finally, pronunciations.

> mergePron
>   :: FilePath
>   -> [((String, Maybe PartOfSpeech), Pronunciation)]
>   -> [Word]
>   -> IO [Word]
> mergePron errF = mergeIO errF getKey print compare match fiddle create
>   where
>     getKey w = (spelling w, part_of_speech w)
> 
>     print (w, Nothing) = w
>     print (w, Just q)  = w ++ " (" ++ writeDictFormat q ++ ")"
> 
>     match (stem, Nothing)  w = stem == spelling w
>     match (stem, Just pos) w = and
>       [ stem == spelling w
>       , or
>         [ Just pos == part_of_speech w
>         , Nothing  == part_of_speech w
>         ]
>       ]
> 
>     fiddle w ((stem,pos),pron) = case pronunciation w of
>         Nothing -> return $ w { pronunciation = Just pron }
>         Just u -> do
>           if u == pron
>             then return w
>             else do
>               tell $ return $ intercalate "\t"
>                 [ "Pronunciation"
>                 , "stem: \"" ++ stem ++ "\""
>                 , "pos: \"" ++ show pos ++ "\""
>                 , "new: \"" ++ writeDictFormat pron ++ "\""
>                 , "old: \"" ++ writeDictFormat u ++ "\""
>                 ]
>               return w
> 
>     create (stem, pos) pron = Word
>       { spelling       = stem
>       , part_of_speech = pos
>       , pronunciation  = Just pron
>       , hyphenation    = Nothing
>       }

Putting it together, ``parseMoby`` merges together all of the Moby data, recording errors to the file ``error-moby.txt``.

> parseMoby :: IO [Word]
> parseMoby = do
> 
>   let errFile = "/home/nathan/code/wordlist/error-moby.txt"
>   writeFile errFile ""
> 
>   putStrLn "parsing database"
>   hyph <- readMobyHyph  "/home/nathan/code/wordlist/moby/mhyph.txt"
>   putStrLn "..mhyph"
>   pos  <- readMobyPOS   "/home/nathan/code/wordlist/moby/mpos.txt"
>   putStrLn "..mpos"
>   pron <- readMobyPron  "/home/nathan/code/wordlist/moby/mpron.txt"
>   putStrLn "..mpron"
>   wrds <- readWords "/home/nathan/code/wordlist/moby/mwords.txt"
>   putStrLn "..mwords"
>
>   putStrLn "merging"
>   return []
>     >>= mergePOS  errFile pos
>     >>= mergeHyph errFile hyph
>     >>= mergePron errFile pron
>     >>= mergeStem errFile wrds

To test what we have so far, ``mainMoby`` writes the consolidated Moby dictionary to ``out-moby.txt``.

> mainMoby :: IO ()
> mainMoby = do
>
>   let outFile = "/home/nathan/code/wordlist/out-moby.txt"
> 
>   dict <- parseMoby
> 
>   writeFile outFile $ unlines $ map writeDictFormat dict
> 
>   putStrLn $ "Words: " ++ show (length dict)
>
>   exitSuccess

After fixing some small errors in the data by hand (reported by our parsers), running ``mainMoby`` produces two files: ``out-moby.txt``, whose lines look like this:

    epiphanize	v-t	ɪ'pɪfʌ,naɪz	e•piph•a•nize
    epiphanized	v-t		e•piph•a•nized
    epiphanizing	v-t		e•piph•a•niz•ing
    epiphanous			
    epiphany	n-s	ɛ'pɪfʌniː	e•piph•a•ny
    epipharyngeal			

And ``error-moby.txt``, whose lines look like this:

    Hyphenation	stem: "zedoary"	new: "zed•o•a•ry"	old: "zed•o•ar•y"
    Hyphenation	stem: "zenith"	new: "ze•nith"	old: "zen•ith"
    Hyphenation	stem: "zincate"	new: "zin•cate"	old: "zinc•ate"
    Pronunciation	stem: "Elie"	pos: "Nothing"	new: "eɪ'liː"	old: "'ɛliː"
    Pronunciation	stem: "ay"	pos: "Just Adverb"	new: "aɪ"	old: "'eɪ"

Woo! ``out-moby.txt`` is a tab-delimited list of words with part of speech, pronunciation, and hyphenation points. It has a *ton* of missing entries, which we can try to fill in later. But at 526462 lines it's a decent start.


Wiktionary
==========

Next we'll use data from Wiktionary to fill as many gaps as we can. Wiktionary is a massive, collaboratively edited database with the goal of collecting every word in every language, and for the popular words in popular languages, it gets pretty close.

I downloaded the [June 20, 2017](https://dumps.wikimedia.org/enwiktionary/20170620/) database dump of the English Wiktionary, which (uncompressed) is a 5.1 GB XML file. But don't let the file format fool you. :) Although the dump is a big XML file with a node for each word, the data *within* each entry is not really structured beyond being marked up with wiki tags and mostly standardized section headings.

I made a shell pipeline using mostly ``sed`` that attempts to cleanly extract as much as possible. It throws out all definitions, since we don't care about those, and without definitions things like synonyms and antonyms don't make sense. We also throw out any information about languages other than English. What's left is a bunch of words, sometimes with pronunciations in one or more dialects, and sometimes with one or more parts of speech attached. It turns out that a large number of entries either are or can "easily" be put into the form

    word (pronunciation)? (noun)? (verb)? (adjective)? (adverb)?

I use ``sed`` to gradually get the entries in this form if possible, and ``awk`` to redirect such entries to a handful of files. Surprisingly (to me) this recovered over 99% of the entries in Wiktionary. This script is kind of a mess, so I'll just refer the interested reader to ``tools/wiki-extract.txt`` in the [repo](https://github.com/nbloomf/wordlist).

Anyway, running that script results in the following files:

1. ``words-only.txt``: These are entries with a stem only, no pronunciation or part of speech.
2. ``pos-only.txt``: These are entries with at least one part of speech but no pronunciation.
3. ``pronunciations-plus.txt``: These are entries with a pronunciation and zero or more parts of speech.
4. ``diff-pron.txt``: These are entries the script recognizes as having different pronunciations depending on the part of speech. I'll leave them alone for now.
5. ``ipa-letters.txt``: These are initialisms; I'll leave them alone for now.
6. ``wiki-words.txt``: These are the entries the script didn't recognize -- the leftovers. 

A lot of the machinery for dealing with the Moby data can be reused; we just need to parse the cleaned up wiki data.

> wikiPOSCode :: String -> Either String PartOfSpeech
> wikiPOSCode c = case c of
>   "noun"      -> Right Noun
>   "verb"      -> Right Verb
>   "adjective" -> Right Adjective
>   "adverb"    -> Right Adverb
>   _ -> Left $ "Unknown part of speech: " ++ c

Parsing the actual file:

> readWikiPOS :: FilePath -> IO [(String, PartOfSpeech)]
> readWikiPOS path = do
>   let
>     makeWord :: String -> String -> Writer [String] [(String, PartOfSpeech)]
>     makeWord !word code =
>       case wikiPOSCode code of
>         Left msg -> do
>           tell [msg]
>           return []
>         Right pos -> do
>           return [( stripSpaces word, pos )]
> 
>     parseRecord :: String -> Writer [String] [(String, PartOfSpeech)]
>     parseRecord !str = do
>       let (stem,pos) = break (== '\t') str
>       fmap concat $ sequence $ map (makeWord $ stripSpaces stem) $ words pos
> 
>   raw <- fmap lines $ readFile path
>   let (dict,err) = runWriter $ fmap concat $ sequence $ map parseRecord raw
>   
>   case err of
>     [] -> return ()
>     _  -> do
>       putStrLn $ "parse errors in " ++ path
>       sequence_ $ map putStrLn err
>       exitFailure
> 
>   return dict

Pronunciations:

> readWikiPron :: FilePath -> IO [((String, Maybe PartOfSpeech), Pronunciation)]
> readWikiPron path = do
>   let
>     makeWord !word pron =
>       return [( (stripSpaces word, Nothing), Pron pron )]
> 
>     makeWordPOS !word pron code =
>       case wikiPOSCode code of
>         Left msg -> do
>           tell [msg]
>           return []
>         Right pos -> do
>           return [( (stripSpaces word, Just pos), Pron pron )]
> 
>     parseRecord !str = do
>       let (stem,rest) = break (== '\t') str
>       let (pron,pos)  = break (== '\t') $ tail rest
>       case words (filter (/= '\t') pos) of
>         [] -> makeWord stem pron
>         ps -> do
>           fmap concat $ sequence
>             $ map (makeWordPOS (stripSpaces stem) (filter (/= '/') pron))
>             $ ps
> 
>   raw <- fmap lines $ readFile path
>   let (dict,err) = runWriter $ fmap concat $ sequence $ map parseRecord raw
>   
>   case err of
>     [] -> return ()
>     _  -> do
>       putStrLn $ "parse errors in " ++ path
>       sequence_ $ map putStrLn err
>       exitFailure
> 
>   return dict

And now ``parseWiki`` attempts to merge the wiki data with a given dictionary.

> parseWiki :: [Word] -> IO [Word]
> parseWiki dict = do
> 
>   let errFile = "/home/nathan/code/wordlist/error-wiki.txt"
>   writeFile errFile ""
> 
>   putStrLn "parsing database"
>   wrds <- readWords     "/home/nathan/code/wordlist/wiki/words-only.txt"
>   putStrLn "..words-only"
>   pos  <- readWikiPOS   "/home/nathan/code/wordlist/wiki/pos-only.txt"
>   putStrLn "..pos-only"
>   pron <- readWikiPron  "/home/nathan/code/wordlist/wiki/pronunciation-plus.txt"
>   putStrLn "..pronunciation-plus"
>
>   putStrLn "merging"
>   return dict
>     >>= mergePOS  errFile pos
>     >>= mergePron errFile pron
>     >>= mergeStem errFile wrds

Putting it all together: ``main`` parses and merges the Moby and Wiki data, writing the result to ``data.txt`` and any errors to ``error-moby.txt`` and ``error-wiki.txt``.

> main :: IO ()
> main = do
>
>   let outFile = "/home/nathan/code/wordlist/dict.txt"
> 
>   dict <- parseMoby >>= parseWiki
> 
>   writeFile outFile $ unlines $ map writeDictFormat dict
> 
>   putStrLn $ "Words: " ++ show (length dict)
>
>   exitSuccess

Running ``main`` yields a dictionary of 1052625 words. I think this will do. Stay tuned for a write up of the project this is all prologue for. :)
