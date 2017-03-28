---
title: Project Euler #1: Multiples of 3 and 5
author: nbloomf
date: 2017-03-05
tags: project-euler, literate-haskell
---

[Problem 1](https://projecteuler.net/problem=1) from Project Euler:

<div class="problem">
If we list all the natural numbers below 10 that are multiples of 3 or 5, we get 3, 5, 6 and 9. The sum of these multiples is 23.

Find the sum of all the multiples of 3 or 5 below 1000.
</div>

First, let's do the most obvious thing: list the integers below 1000, filter out the ones divisible by either 3 or 5, and sum. For reasons I'll get to later I will parameterize this function on $n$, the upper bound for our numbers.

> pe1' :: Integer -> Integer
> pe1' n = sum $ filter div3or5 [1..(n-1)]
>   where
>     div3or5 k = (k`mod`3 == 0) || (k`mod`5 == 0)

We can verify that ``pe1' 10 == 23`` as claimed. Now we can compute the answer to the given problem like so:

```haskell
$> pe1' 1000
233168
```

And done.

But wait! Anything worth doing is worth overdoing, so let's try something less obvious.

Suppose we wanted the sum of the multiples of 3 or 5 less than a bigger bound -- say $n = 10^{10}$. My laptop computes ``pe1' 1000`` in a fraction of a second, but hangs on $10^{10}$. And the reason why is clear: ``pe1' n`` constructs a list $n$ items long and deconstructs it. So the time complexity is roughly $n$.

We can verify this with a little experiment. In GHCi, say ``:set +s`` and the interpreter will report time and memory usage for each computation. The following table summarizes the execution time of ``pe1'`` for several inputs on my machine.

-----------------------------------
``n``   ``pe1' n``        Time (s)
------  -----------       -----
$10^2$  2318              0.01

$10^3$  233168            0.02

$10^4$  23331668          0.06

$10^5$  2333316668        0.46

$10^6$  233333166668      4.55

$10^7$  23333331666668    45.38

$10^8$  my laptop choked!
-----------------------------------

Two things jump out at me: first, there's a pattern in the values, which I was not expecting. Second, and more germane, the time seems to increase by a factor of 10 from row to row after $n = 10^4$. (Below this $n$ I suspect the time is dominated by the time required to print the output.) So the complexity is $O(n)$.


Can we do better?
-----------------

Let's break the problem down a little. We want the sum of all numbers less than $n$ which are divisible by either 3 or 5; let's start with something simpler: the sum of all the numbers less than $n$ which are divisible by 3.

The sum of the first $k$ multiples of 3 is $$3 + 6 + 9 + \cdots + 3k = 3(1 + 2 + 3 + \cdots + k) = 3 \frac{k(k+1)}{2},$$ using the formula for the $k$th [triangular number](https://en.wikipedia.org/wiki/Triangular_number). Now how many multiples of 3 are there below $n$? This is exactly what is counted by the quotient in integer division. That is, given positive integers $a$ and $b$, when we decompose $a$ as $a = qb + r$ using the division algorithm with $r >= 0$, that $q$ is precisely the number of numbers between 1 and $a$ (inclusive) which are divisible by $b$. The Haskell function to find this quotient is (shockingly) ``quot``.

But there's nothing magic about 3 in that analysis; we might as well replace 3 with any other positive integer, say $t$. Then we can sum the multiples of $t$ below $n$ like so.

> sumMultsOfBelow :: Integer -> Integer -> Integer
> sumMultsOfBelow t n = t * q * (q+1) `quot` 2
>   where q = (n-1) `quot` t

What is the complexity of ``sumMultsOfBelow``? It's harder to say exactly, because I don't know how ``quot`` is implemented. But the schoolbook algorithm for integer division is bounded above by $O(\log(n)^2)$; this is much cheaper than $O(n)$.

So we can easily find the sum of the multiples of 3 below 1000 and the multiples of 5 below 1000:

```haskell
$> (sumMultsOfBelow 3 1000) + (sumMultsOfBelow 5 1000)
266333
```

But this doesn't agree with the more naive (but clearly correct) ``pe1'``. And it's not too hard to see why -- the sets of multiples of 3 and multiples of 5 are not disjoint, so some numbers are being included twice in the sum. Which ones? Well, the numbers that are divisible by both 3 and 5, which are precisely the multiples of their least common multiple, 15. And sure enough, if we account for those...

```haskell
$> (sumMultsOfBelow 3 1000) + (sumMultsOfBelow 5 1000) - (sumMultsOfBelow 15 1000)
233168
```

Let's wrap this in a definition.

> pe1'' :: Integer -> Integer
> pe1'' n = (sumMultsOfBelow 3 n)
>             + (sumMultsOfBelow 5 n)
>             - (sumMultsOfBelow 15 n)

At this point, I was planning to include another table of timings to show how much faster ``pe1''`` is, but I had to go to $n = 10^{85}$ before it took longer than 0.01 seconds (the smallest unit of time reported by GHCi). For reference, ``pe1'' (10^100000)`` took 2.03 seconds on my machine. An $O(n)$ algorithm has no hope on inputs that big. And by the way that digit pattern, a 2, followed by 3s, then 1, then 6s, then 8, holds.

Before we get too excited, let's verify that ``pe1'`` and ``pe1''`` agree, at least on small inputs.

> test_pe1 :: Integer -> Bool
> test_pe1 n = pe1' n == pe1'' n

And then:

```haskell
$> and $ map test_pe1 [1..1500]
True
```

So it is with confidence we say that ``pe1'`` and ``pe1''`` are the same function. Then the answer to problem 1 is:

> pe1 :: Integer
> pe1 = pe1'' 1000
