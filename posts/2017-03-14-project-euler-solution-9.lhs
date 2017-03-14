---
title: Project Euler #9: Special Pythagorean Triplet
author: nbloomf
date: 2017-03-14
tags: project-euler
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-03-14-project-euler-solution-9.lhs) into GHCi and play along.

[Problem 9](https://projecteuler.net/problem=9) from Project Euler:

<div class="problem">
A Pythagorean triplet is a set of three natural numbers, $a < b < c$, for which
$a^2 + b^2 = c^2$.

For example, $$3^2 + 4^2 = 9 + 16 = 25 = 5^2.$$

There exists exactly one Pythagorean triplet for which $a + b + c = 1000$.
Find the product $abc$.
</div>

<div class="result">
<div class="thm">
Every Pythagorean triple is of the form $$a = k(m^2 - n^2)$$, $$b = 2kmn$$, $$c = k(m^2 + n^2)$$ for some unique positive integers $m$, $n$, and $k$, where $m > n$, and with $m$ and $n$ are coprime and not both odd.
</div>
</div>
