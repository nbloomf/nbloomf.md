---
title: "Project Euler #5: Smallest Multiple"
author: nbloomf
date: 2017-03-10
tags: project-euler, literate-haskell
---

First some boilerplate.

> module ProjectEuler005 where

[Problem 5](https://projecteuler.net/problem=5) from Project Euler:

<div class="problem">
2520 is the smallest number that can be divided by each of the numbers from 1 to 10 without any remainder.

What is the smallest positive number that is evenly divisible by all of the numbers from 1 to 20?
</div>

The smallest natural number $k$ that is divisible by natural numbers $a$ and $b$ is called their *least common multiple*; we'll denote this by $a \wedge b$.

The inverse notion, the *largest* natural number that *divides* both $a$ and $b$, is called their *greatest common divisor*; we'll denote this by $a \vee b$.

As operations, the LCM and GCD have lots of nice properties. But two are important for us. For all natural numbers $a$, $b$, and $c$, we have the following.

1. $a \wedge b = \frac{ab}{a \vee b}$
2. $a \wedge (b \wedge c) = (a \wedge b) \wedge c$

The first property says that the LCM can be computed easily if we know the GCD. This is useful because there is a nice algorithm, called the Euclidean Algorithm, for computing GCDs.

<div class="result">
<div class="thm">
Let $a$ and $b$ be natural numbers, and let $q$ and $r$ be natural numbers such that $a = qb+r$ and $0 \leq r < b$. Then $a \vee b = b \vee r$.
</div>
</div>

What makes the Euclidean Algorithm so nice is that, combined with the Well-Ordering Property of the natural numbers, it gives us a recursive algorithm for computing GCDs.

> (\/), (/\) :: Integer -> Integer -> Integer
> 
> a \/ 0 = a
> a \/ b = b \/ (a`rem`b)
> 
> a /\ b = (a*b)`div`(a \/ b)

The second property above says that if we want to find the LCM of a bunch of integers, we can do so pairwise, and it doesn't matter what order we do this in. For instance, using ``foldr1``:

> lcms :: [Integer] -> Integer
> lcms = foldr1 (/\)

Now ``lcms`` will take a nonempty list of positive integers and compute their least common multiple.

```haskell
$> lcms [1..10]
2520
```

The Euclidean Algorithm is pretty snappy. Just for fun, here are some timings.

-------------------------------
``k``  ``lcms [1..(k*10^4)]``
------ -----------------------
1      0.26 s

2      0.74 s

3      1.76 s

4      2.67 s

5      4.26 s

6      5.63 s

7      7.81 s

8      9.51 s

9      11.24 s
-------------------------------

Anyway, the final answer is:

> pe5 :: Integer
> pe5 = lcms [1..20]
> 
> main :: IO ()
> main = putStrLn $ show pe5
