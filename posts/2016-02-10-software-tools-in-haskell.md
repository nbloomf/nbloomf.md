---
title: Software Tools in Haskell
author: nbloomf
date: 2016-02-10
---

*Software Tools* is a little book about tool building by Brian Kernighan and P. J. Plauger. It's a classic, and people far more qualified than me have written very positive reviews of it. The book includes several example programs, which are designed individually to solve simple problems and collectively to work together readily to solve larger problems.

I've written some small tools for my own use, the largest of which (by far) is the feivel templating language. But I'm not particularly good at it, and would like to improve. So I will be reading through *Software Tools* and porting the examples to Haskell.

Because I enjoy pain, all of this will be done publicly, with code hosted at [GitHub](http://github.com/nbloomf/st-haskell) and narrative documentation posted here.


## Ground Rules

> Okay, let's party. But first, let's go over the rules, because what is fun without the rules?
> <cite>Gru in "Despicable Me"</cite>

The purpose of this project is to learn, and so there are some self-imposed rules.

1. Reproduce the behavior of the original tools as closely as possible. (Possibly with extensions.)
2. Write code which is idiomatic Haskell, but follows the spirit of the originals and doesn't try to be too clever.
3. Produce executable programs which interact with my own working environment.
4. Follow established conventions regarding things like command-line arguments and return codes.
5. Include tests.

I will prefix the names of these ports with ``sth-``, to avoid clashing with existing real programs.


## The Posts (Chrono Order)

* [``copy``, ``charcount``, ``linecount``](/posts/2016-02-11-software-tools-in-haskell-copy-charcount-linecount.html)

## The Tools (Alpha Order)

* [``charcount``](/posts/2016-02-11-software-tools-in-haskell-copy-charcount-linecount.html#charcount): count characters on stdin
* [``copy``](/posts/2016-02-11-software-tools-in-haskell-copy-charcount-linecount.html#copy): copy characters from stdin to stdout
* [``linecount``](/posts/2016-02-11-software-tools-in-haskell-copy-charcount-linecount.html#linecount): count lines on stdin


## Why Haskell?

The programs in *Software Tools* are written in [Ratfor](https://en.wikipedia.org/wiki/Ratfor), a purpose-built extension of Fortran with control-flow statements. (At the time, control flow in Fortran was done by hand with GOTO.) Kernighan and Plauger explain that this was a pragmatic choice, as no language at the time had the right mix of ubiquity and expressiveness. With 40 years(!) of hindsight, though, I'd say that this was an inspired choice. Books written in real languages quickly become hopelessly outdated. But books written in toy languages can focus on timeless principles. *TAOCP* by Knuth (which I've never read) and *Functional Programming: Practice and Theory* by MacLennan (which I have) are positive examples of this, and I have a shelf full of nameless algebra books written in APL and Pascal to serve as negative examples.

So why Haskell. I work in academia -- in math, not in CS -- and producing software doesn't even show up on the list of things I am supposed to do. That means I can use whatever tools and languages I want to. Well, I've been using Haskell for several years as a "[tool of thought](www.jsoftware.com/papers/tot.htm)", to paraphrase Ken Iverson, mostly for one-off experiments. Haskell is good for that, and I find that it fits my problem-solving style very well. (Programs are arrows in a category? Of course!) But I want to improve my ability to write "real" programs in the language. So here we are.

