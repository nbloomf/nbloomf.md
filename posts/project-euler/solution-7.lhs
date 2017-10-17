---
title: Project Euler #7: 10001st Prime
author: nbloomf
date: 2017-03-12
tags: project-euler, literate-haskell
---

First some boilerplate.

> module ProjectEuler007 where

[Problem 7](https://projecteuler.net/problem=7) from Project Euler:

<div class="problem">
By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13, we can see that the 6th prime is 13.

What is the 10001st prime number?
</div>

We already wrote a utility to list the primes for [Problem 3](/posts/2017-03-07-project-euler-solution-3.html):

> isprime :: Integer -> Bool
> isprime n = all (\p -> n`rem`p /= 0) $
>   takeWhile (\p -> p^2 <= n) primes
> 
> primes :: [Integer]
> primes = 2 : filter isprime [3,5..]

There is no (known, useful) formula for generating the $n$th prime, so I'll just take the 10001th entry of ``primes``.

> pe7' :: Integer -> Integer
> pe7' n = elt_at n primes
>   where
>     elt_at :: Integer -> [a] -> a
>     elt_at n (x:xs) = if n == 1
>       then x
>       else elt_at (n-1) xs

woo

So the final answer is

> pe7 :: Integer
> pe7 = pe7' 10001
> 
> main :: IO ()
> main = putStrLn $ show pe7
