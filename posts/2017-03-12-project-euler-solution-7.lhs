---
title: Project Euler #7: 10001st Prime
author: nbloomf
date: 2017-03-12
tags: project-euler
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-03-12-project-euler-solution-7.lhs) into GHCi and play along.

[Problem 7](https://projecteuler.net/problem=7) from Project Euler:

<div class="problem">

</div>

We already wrote a utility to list the primes for [Problem 3](/posts/2017-03-07-project-euler-solution-3.html):

```haskell

> isprime :: Integer -> Bool
> isprime n = all (\p -> n`rem`p /= 0) $
>   takeWhile (\p -> p^2 <= n) primes
> 
> primes :: [Integer]
> primes = 2 : filter isprime [3,5..]

```

There is no (known, useful) formula for generating the $n$th prime, so I'll just take the 10001th entry of ``primes``.

```haskell

> pe7' :: Integer -> Integer
> pe7' n = elt_at n primes
>   where
>     elt_at :: Integer -> [a] -> a
>     elt_at n (x:xs) = if n == 1
>       then x
>       else elt_at (n-1) xs

```

woo

So the final answer is 

```haskell

> pe7 :: Integer
> pe7 = pe7' 10001

```
