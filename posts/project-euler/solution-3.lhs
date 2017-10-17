---
title: Project Euler #3: Largest Prime Factor
author: nbloomf
date: 2017-03-07
tags: project-euler, literate-haskell
---

First some boilerplate.

> module ProjectEuler003 where

[Problem 3](https://projecteuler.net/problem=3) from Project Euler:

<div class="problem">
The prime factors of 13195 are 5, 7, 13 and 29.

What is the largest prime factor of the number 600851475143?
</div>

Let's start by writing two helper functions: ``isprime``, which detects whether a given integer is prime, and ``primes``, the list of positive prime integers. We'll use the following characterization of the prime positive integers: 2 is prime, and an integer $n$ is prime if it is not evenly divisible by any of the primes $p$ with $p^2 \leq n$.

That sounds circular (the primes are those integers not divisible by any smaller primes) but thanks to the well-ordering property of the natural numbers, it's kosher. Even better, this definition translates directly to code.

> isprime :: Integer -> Bool
> isprime n = all (\p -> n`rem`p /= 0) $
>   takeWhile (\p -> p^2 <= n) primes
> 
> primes :: [Integer]
> primes = 2 : filter isprime [3,5..]

Now we have a list of all the primes in order.

```haskell
$> take 10 primes
[2,3,5,7,11,13,17,19,23,29]
```

This is absolutely not the most efficient way to construct the primes, but it has the advantage of being both simple and clearly correct. Building a blazing fast prime sieve is beyond the scope of my itch scratching for the moment, so I'll leave it there.

So this problem is asking for the largest prime factor of an integer. I happen to know that this is a Hard Problem; so hard, in fact, that cryptographic schemes are built on the premise that finding the largest prime factor of an arbitrary (large) integer is infeasible. All that is to say -- I won't bother trying to be clever, and just do the obvious thing: given $n$, find all of its prime factors, and just return the largest one.

> -- find the smallest prime p with n = pm
> -- return (p,m)
> first_factor :: Integer -> (Integer, Integer)
> first_factor n = check $ takeWhile (\p -> p^2 <= n) primes
>   where
>     check [] = (n,1)
>     check (p:ps) = if n`rem`p == 0
>       then (p, n`quot`p)
>       else check ps
> 
> -- prime factors of n in nondecreasing order
> factor :: Integer -> [Integer]
> factor n = let (p,m) = first_factor n in
>   if m == 1 then [p] else p : factor m

This implementation of ``factor`` does a lot of unnecessary work; each time we call ``smallest_factor``, it tests a bunch of prime divisors that we know in advance won't work. But it does the job.

> pe3' :: Integer -> Integer
> pe3' n = last $ factor n

Testing:

```haskell
$> pe3' 10
5
$> pe3' (2^100)
2
$> pe3' 600851475143
6857
```

So the final answer is:

> pe3 :: Integer
> pe3 = pe3' 600851475143
> 
> main :: IO ()
> main = putStrLn $ show pe3
