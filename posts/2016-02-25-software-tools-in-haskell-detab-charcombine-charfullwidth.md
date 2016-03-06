---
title: Software Tools in Haskell: detab, charcombine, charfullwidth
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

* The input consists of lines, separated by ``\n``s, each of which has several fields, separated by ``\t``s. The final output line will be terminated by a newline, even if the final input line was not. (So ``detab`` is a line-oriented filter.)
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

This program is quite a bit more complicated than the ones we've written so far because it needs to take command line arguments from the user. That means parsing structured input (here, base 10 natural numbers) and the possibility of input errors. My version of this program is pretty long compared to the *Software Tools* example, but it does have extra functionality; namely custom tab stop widths. (NB: reading further in the text, adding this functionality to ``detab`` is Exercise 2-4 in the book. Oops!)

First, here is the main program.


```haskell
-- sth-detab: convert tabs to spaces
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
  lineFilter (convertTabStops ts)
  exitSuccess
```


In order, we (1) get the user-supplied tab stop widths as strings (``getArgs``), then (2) parse these as positive integers (``readPosIntList``), which may fail. We have a custom library function (``convertTabStops``) that does the real work, and here (3) define a throwaway function ``detab`` that wraps ``convertTabStops`` and handles its error condition (more on that later). Finally, we (4) read from stdin lazily, split the input into lines, and apply ``detab`` to each one.

This program has an error condition: the user may provide bad command line arguments. In this case we gently remind the user how to use this program. We follow the standard unix practice of writing errors to stderr rather than stdout. Since we'll be reporting errors more in the future, we'll write two library functions two write messages to stderr.


```haskell
putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr


reportErrorMsgs :: [String] -> IO ()
reportErrorMsgs errs = do
  name <- getProgName
  sequence_ $ map putStrLnErr $ ((name ++ " error"):errs)
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


filterMaybe :: (a -> Bool) -> Maybe a -> Maybe a
filterMaybe p x = do
  y <- x
  case p y of
    True  -> Just y
    False -> Nothing
```


``readDecimalNat`` takes a string of decimal digits and converts it to a natural number (negatives are not handled). Or, rather, converts to a ``Maybe Int``. Conversion will fail if the input string does not consist of only characters 0 through 9; in this case the function returns ``Nothing``. (We don't see an explicit ``Nothing`` in the code because it is implicitly returned by the standard library function ``lookup``.) Then ``readPosIntList`` simply applies ``readDecimalNat`` to a list of strings, and makes sure the numbers returned are all positive. This is where ``guardMaybe`` comes in.

Next we show ``convertTabStops``.


```haskell
convertTabStops :: [Int] -> String -> String
convertTabStops [] xs = xs
convertTabStops ks xs = accum [] ks xs
  where
    accum zs _   "" = concat $ reverse zs
    accum zs [t] ys =
      let (as,bs) = splitTabStop t ys in
      accum (as:zs) [t] bs
    accum zs (t:ts) ys =
      let (as,bs) = splitTabStop t ys in
      accum (as:zs) ts bs

    splitTabStop :: Int -> String -> (String, String)
    splitTabStop k xs
      | k <= 0    = (xs,"")
      | otherwise = 
          case spanAtMostWhile k (/= '\t') xs of
            (as,"") -> (stripTrailingSpaces as, "")
            (as,bs) -> let cs = padToByAfter k ' ' as in
              case bs of
                '\t':ds -> (cs,ds)
                ds      -> (cs,ds)
      where
        stripTrailingSpaces = reverse . dropWhile (==' ') . reverse


spanAtMostWhile :: Int -> (a -> Bool) -> [a] -> ([a],[a])
spanAtMostWhile k p xs
  | k < 0     = ([],xs)
  | otherwise = acc k [] xs
  where
    acc 0 as bs = (reverse as, bs)
    acc _ as [] = (reverse as, [])
    acc t as (b:bs) = if p b
      then acc (t-1) (b:as) bs
      else (reverse as, b:bs)


padToByAfter :: Int -> a -> [a] -> [a]
padToByAfter k z xs = take k (xs ++ repeat z)
```


The helper function ``splitTabStop`` takes a single tab stop width ``k`` and a string ``xs``, and peels of the first ``k`` characters of ``xs`` unless one of them is a ``\t``. It then returns a pair consisting of the peeled off characters and the remainder of the string. (If the ``k`` parameter is negative, we have a problem, so we return ``Nothing`` in this case. **This is why we have to handle the second error condition in the main function.** If Haskell had a convenient positive integer type, this could be dealt with differently.) Then ``convertTabStops`` simply marches down an entire line with a list of tab stop widths, peeling off tab stops as it goes. This is done using an accumulating parameter function, ``accum``. Once the string is empty, ``accum`` reverses the accumulating parameter and returns it (concatenated), otherwise it takes the next tab stop width and repeats.

``spanAtMostWhile`` is a combination of the standard library functions ``span`` and ``take``. It peels off up to ``k`` elements of a list provided they all satisfy predicate ``p`` and returns both the peeled off elements and the remainder of the list. ``padToByAfter`` pads lists to a given length with a given character, throwing an error if the given length is already too long. Both of these are general enough to factor out; they also both use the accumulating parameter style to avoid space leaks.



<a name="charcombine" />

## ``charcombine``: replace combining unicode characters with precomposed characters

One of the fundamental problems with our ``detab`` program is that it assumes plain text characters can be displayed on a rectangular array of character cells in a one-to-one way, with each character taking one cell and each cell having at most one character. This was a reasonable expectation at the time *Software Tools* was written, when character encodings were simpler. But Unicode makes this assumption wrong for several reasons. The first, which we will address now, is that *diacritics* like acute accents or carons can be expressed using *combining characters*. These are special unicode code points that are not displayed independently but rather modify the character which they succeed. You can read more about these on the [wiki](https://en.wikipedia.org/wiki/Combining_character). This is a problem for us because ``detab`` counts tab stop widths in terms of characters.

There is something we can do to fix this. Unicode also includes a large number of *precomposed* characters; single code points that are semantically equivalent to characters with combining diacritics. For example, code point ``U+0041`` (latin capital A) followed by ``U+0301`` (combining acute accent above) is canonically equivalent to the single code point ``U+00C1`` (latin capital A with acute accent above). There is a helpful [wiki page](https://en.wikipedia.org/wiki/List_of_precomposed_Latin_characters_in_Unicode) with a list of these precombined characters.

We could make ``detab`` aware of this equivalence. This is a bad idea, though, for a few reasons. First, it would make ``detab`` more complicated with only marginal benefit. Most of the text that I work with is plain ASCII, and making ``detab`` fiddle with unicode issues on such files will slow it down for no reason. We could give ``detab`` a command line flag to explicitly enable this feature, but it is important not to clutter up the interface of a program without a good reason. Second, ``detab`` is surely not the only program that might need to deal with this unicode issue. If each one solves the problem in its own way there will be lots of duplicated code, and duplicated code (while sometimes justifiable) is a breeding ground for bugs. Moreover the Unicode standard changes every few years, possibly requiring a time consuming edit of all the programs that work with unicode-encoded text. **A far better solution is to make a separate program, ``charcombine``, to handle this problem.** Because our programs are designed to communicate via stdin and stdout, then we can send text through ``charcombine`` before giving it to ``detab``. This way ``detab`` can stay simple, and ``charcombine`` can be a small, general-purpose tool for replacing combining characters with precomposed characters.

Since we already have a function, ``getGlyphs``, which splits a stream of characters into noncombining+combining substrings, the main function of ``charcombine`` is quite succinct.


```haskell
-- sth-charcombine: replace combining unicode chars with precomposed chars
--   character-oriented

module Main where

import SoftwareTools.Lib (exitSuccess)
import SoftwareTools.Lib.IO   (charFilter)
import SoftwareTools.Lib.Text (getGlyphs)

main :: IO ()
main = do
  charFilter (concatMap toPrecomposed . getGlyphs)
  exitSuccess
```


All that remains is to write a function, ``composeGlyph``, that takes a string of characters and replaces it by an equivalent precomposed character.


```haskell
toPrecomposed :: String -> String
toPrecomposed ""  = ""
toPrecomposed [c] = [c]
toPrecomposed [x, '\x0301'] = case lookup x acute of
  Just y  -> y
  Nothing -> [x, '\x0301']
  where
    acute =
      [ ('A',"Á"), ('Æ',"Ǽ"), ('C',"Ć"), ('E',"É"), ('G',"Ǵ")
      , ('I',"Í"), ('K',"Ḱ"), ('L',"Ĺ"), ('M',"Ḿ"), ('N',"Ń")
      , ('O',"Ó"), ('Ø',"Ǿ"), ('P',"Ṕ"), ('R',"Ŕ"), ('S',"Ś")
      , ('U',"Ú"), ('W',"Ẃ"), ('Y',"Ý"), ('Z',"Ź")
      , ('a',"á"), ('æ',"ǽ"), ('c',"ć"), ('e',"é"), ('g',"ǵ")
      , ('i',"í"), ('k',"ḱ"), ('l',"ĺ"), ('m',"ḿ"), ('n',"ń")
      , ('o',"ó"), ('ø',"ǿ"), ('p',"ṕ"), ('r',"ŕ"), ('s',"ś")
      , ('u',"ú"), ('w',"ẃ"), ('y',"ý"), ('z',"ź")
      ]
toPrecomposed x = x
```


And OH MY GOSH THIS IS SO BORING. There are dozens more precomposed characters, and it's pretty clear how to extend this function to those. I will leave finishing this to another day.



<a name="charfullwidth" />

## ``charfullwidth``: replace characters with fullwidth equivalents

Replacing "normal" characters with fullwidth forms is much simpler. We reuse the structure of ``copy``, with a filter to map characters.


```haskell
-- sth-charfullwidth: replace characters with fullwidth equivalents
--   character-oriented

module Main where

import SoftwareTools.Lib (exitSuccess)
import SoftwareTools.Lib.IO   (charFilter)
import SoftwareTools.Lib.List (applyListMap)


main :: IO ()
main = do
  charFilter (map toFullwidth)
  exitSuccess
```


And the map:


```haskell
toFullwidth :: Char -> Char
toFullwidth x = case lookup x full of
  Just y  -> y
  Nothing -> x
  where
    full =
      [ ('!','！'), ('"','＂'),  ('#','＃'), ('$','＄'), ('%','％')
      , ('&','＆'), ('\'','＇'), ('(','（'), (')','）'), ('*','＊')
      , ('+','＋'), (',','，'),  ('-','－'), ('.','．'), ('/','／')
      , ('0','０'), ('1','１'),  ('2','２'), ('3','３'), ('4','４')
      , ('5','５'), ('6','６'),  ('7','７'), ('8','８'), ('9','９')
      , (':','：'), (';','；'),  ('<','＜'), ('=','＝'), ('>','＞')
      , ('?','？'), ('@','＠'),  ('A','Ａ'), ('B','Ｂ'), ('C','Ｃ')
      , ('D','Ｄ'), ('E','Ｅ'),  ('F','Ｆ'), ('G','Ｇ'), ('H','Ｈ')
      , ('I','Ｉ'), ('J','Ｊ'),  ('K','Ｋ'), ('L','Ｌ'), ('M','Ｍ')
      , ('N','Ｎ'), ('O','Ｏ'),  ('P','Ｐ'), ('Q','Ｑ'), ('R','Ｒ')
      , ('S','Ｓ'), ('T','Ｔ'),  ('U','Ｕ'), ('V','Ｖ'), ('W','Ｗ')
      , ('X','Ｘ'), ('Y','Ｙ'),  ('Z','Ｚ'), ('[','［'), ('\\','＼')
      , (']','］'), ('^','＾'),  ('_','＿'), ('`','｀'), ('a','ａ')
      , ('b','ｂ'), ('c','ｃ'),  ('d','ｄ'), ('e','ｅ'), ('f','ｆ')
      , ('g','ｇ'), ('h','ｈ'),  ('i','ｉ'), ('j','ｊ'), ('k','ｋ')
      , ('l','ｌ'), ('m','ｍ'),  ('n','ｎ'), ('o','ｏ'), ('p','ｐ')
      , ('q','ｑ'), ('r','ｒ'),  ('s','ｓ'), ('t','ｔ'), ('u','ｕ')
      , ('v','ｖ'), ('w','ｗ'),  ('x','ｘ'), ('y','ｙ'), ('z','ｚ')
      , ('{','｛'), ('|','｜'),  ('}','｝'), ('~','～')
      ]
```

This probably looks terrible in your browser because unicode coverage.
