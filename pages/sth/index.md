---
title: Software Tools in Haskell
author: nbloomf
---

*Software Tools* is a little book about tool building by Brian Kernighan and P. J. Plauger. It's a classic, and people far more qualified than me have written very positive things about it. The book includes several example programs which are designed individually to solve simple problems and collectively to work together readily to solve larger problems.

I've written some small tools for my own use, the largest of which (by far) is the feivel templating language. But I'm not particularly good at it and would like to improve. So I will be reading through *Software Tools* and porting the examples to Haskell. Along the way, I expect to supplement the text's examples with tools to solve my own problems.

Because I enjoy pain, all of this will be done publicly, with code hosted at [GitHub](http://github.com/nbloomf/st-haskell) and narrative documentation posted here.


## Ground Rules

> Okay, let's party. But first, let's go over the rules, because what is fun without the rules?
> <cite>Gru in *Despicable Me 2*</cite>

The purpose of this project is to learn, and so there are some self-imposed rules. (Subject to change.)

1. Produce working tools.
2. Follow established conventions regarding things like command-line arguments and return codes.
3. Think very hard before making a tool less consistent or more complicated.

I will prefix the names of these ports with ``sth-``, to avoid clashing with existing real programs. And of course all should be considered works-in-progress. These tools operate on text, which turns out to be [more interesting](/pages/sth/formats.html) than I realized when I started this project.


## The Tools (Book Order)

* [``noop``](/posts/software-tools-in-haskell/noop.html): exit successfully

### Chapter 1: Getting Started

* [``copy``](/posts/software-tools-in-haskell/copy.html): copy characters from ``stdin`` to ``stdout``
* [``count``](/posts/software-tools-in-haskell/count.html): count lines or chars on ``stdin``
* [``wordcount``](/posts/software-tools-in-haskell/wordcount.html): count words on ``stdin``
* [``sentcount``](/posts/software-tools-in-haskell/sentcount.html): count sentences on ``stdin``
* [``glyphcount``](/posts/software-tools-in-haskell/glyphcount.html): count glyphs on ``stdin``
* [``detab``](/posts/software-tools-in-haskell/detab.html): replace tabs on ``stdin`` with spaces
* [``charcombine``](/posts/software-tools-in-haskell/charcombine.html): replace chars on ``stdin`` with precomposed equivalents
* [``charfullwidth``](/posts/software-tools-in-haskell/charfullwidth.html): replace chars on ``stdin`` with fullwidth equivalents

### Chapter 2: Filters

* [``entab``](/posts/software-tools-in-haskell/entab.html): replace spaces on ``stdin`` with tabs
* [``echo``](/posts/software-tools-in-haskell/echo.html): write arguments to ``stdout``
* [``overstrike``](/posts/software-tools-in-haskell/overstrike.html): interpret backspaces on ``stdin``
* [``unescape``](/posts/software-tools-in-haskell/unescape.html): interpret escape codes on ``stdin``
* [``escape``](/posts/software-tools-in-haskell/escape.html): replace strange chars on ``stdin`` with escape sequences
* [``compress``](/posts/software-tools-in-haskell/compress.html): compress text on ``stdin`` (run length encoding)
* [``expand``](/posts/software-tools-in-haskell/expand.html): uncompress text on ``stdin`` (run length encoding)
* [``crypt``](/posts/software-tools-in-haskell/crypt.html): xor text on ``stdin`` with a list of keys
* [``translit``](/posts/software-tools-in-haskell/translit.html): transliterate or remove chars on ``stdin``
* [``charreplace``](/posts/software-tools-in-haskell/charreplace.html): replace chars by strings on ``stdin``
* [``tail``](/posts/software-tools-in-haskell/tail.html): get the last k lines or chars from ``stdin``
* [``getlines``](/posts/software-tools-in-haskell/getlines.html): extract lines from ``stdin`` by index

### Chapter 3: Files

* [``compare``](/posts/software-tools-in-haskell/compare.html): find the first position where two text streams differ
* [``import``](/posts/software-tools-in-haskell/import.html): splice contents of a file into ``stdin``
* [``concat``](/posts/software-tools-in-haskell/concat.html): concatenate files
* [``wye``](/posts/software-tools-in-haskell/wye.html): write ``stdin`` to files and ``stdout``
* [``pslineprint``](/posts/software-tools-in-haskell/pslineprint.html): print ``stdin`` to postscript
* [``paginate``](/posts/software-tools-in-haskell/paginate.html): format lines with page numbers and headers
* [``examine``](/posts/software-tools-in-haskell/examine.html): interactively view a file
* [``archive``](/posts/software-tools-in-haskell/archive.html): bundle text files
* [``linenumber``](/posts/software-tools-in-haskell/linenumber.html): number lines on ``stdin``

### Chapter 4: Sorting

* [``bubble``](/posts/software-tools-in-haskell/bubble.html): (bubble)sort lines on stdin


## Why Haskell?

The programs in *Software Tools* are written in [Ratfor](https://en.wikipedia.org/wiki/Ratfor), a purpose-built extension of Fortran with control-flow statements. (At the time, control flow in Fortran was done by hand with GOTO.) Kernighan and Plauger explain that this was a pragmatic choice, as no language at the time had the right mix of ubiquity and expressiveness. With 40 years(!) of hindsight, though, I'd say that this was an inspired choice. Books written in real languages quickly become hopelessly outdated. But books written in toy languages can focus on timeless principles. *TAOCP* by Knuth (which I've never read) and *Functional Programming: Practice and Theory* by MacLennan (which I have) are positive examples of this, and I have a shelf full of nameless algebra books written in APL and Pascal to serve as negative examples.

So why Haskell. I've been using Haskell for several years as a "[tool of thought](http://www.jsoftware.com/papers/tot.htm)", to paraphrase Ken Iverson, mostly for one-off experiments. Haskell is good for that, and I find that it fits my problem-solving style very well. (Programs are arrows in a category? Of course!) But I want to improve my ability to write "real" programs in the language. So here we are.
