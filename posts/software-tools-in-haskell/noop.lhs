---
title: "Software Tools in Haskell: noop"
subtitle: exit successfully
author: nbloomf
date: 2016-02-08
tags: software-tools-in-haskell, literate-haskell
---

As usual, we start with some imports.

> -- sth-noop: exit successfully
> module Main where
> 
> import System.Exit (exitSuccess)

One of the most important things a program can do is exit successfully when it is finished. This is what (all, really) that ``noop`` does.

> main :: IO ()
> main = do
>   -- real tools do stuff here
>   exitSuccess

This program doesn't compute anything, so in that sense it's not much of a tool. But it does illustrate the basic structure of a Haskell program. The ``main`` function is what gets executed when a program is run; everything else (parsing command line arguments, reading files, whatever) is done within ``main``. We signal that the program has exited successfully with the aptly-named ``exitSuccess`` function.
