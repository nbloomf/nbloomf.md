---
title: Programs from Theorems
author: nbloomf
date: 2017-02-28
tags: haskell
---

Some years ago I read a [blog post](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html) by Dan Piponi which includes the following statement:

> So here's a way to write code: pick a theorem, find the corresponding type, and find a function of that type.

Dan then takes a result known as [Loeb's Theorem](https://en.wikipedia.org/wiki/L%C3%B6b's_theorem) in modal logic and shows how one "implementation" of this theorem acts like a spreadsheet evaluator. (!) At the time I remember thinking this was pretty neat, but the depth of this strategy for finding useful abstractions went over my head.

More recently I've found myself teaching mathematical logic to undergraduate students, so some of these ideas are back in my head again. I decided to take another look at turning logic theorems into programs. I don't have a book on intuitionist logic handy, but helpfully 
