---
title: Project Euler Solution #4: Largest Palindrome Product
author: nbloomf
date: 2017-03-08
tags: project-euler
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-03-07-project-euler-solution-4.lhs) into GHCi and play along.

```haskell

> import Data.List

```

[Problem 4](https://projecteuler.net/problem=4) from Project Euler:

<div class="problem">

A palindromic number reads the same both ways. The largest palindrome made from the product of two 2-digit numbers is 9009 = 91 × 99.

Find the largest palindrome made from the product of two 3-digit numbers.
</div>

The property of being a palindrome is very different from most interesting properties of numbers; it is not inherent to the number, but rather an artifact of one of many possible *representations* of the number. In this case, the representation in base 10.

The first thing I'll do is write a helper function to find the digits of an integer in base 10.

```haskell

> -- base 10 digits of n in 'little endian' order
> -- (least significant digits first)
> base10 :: Integer -> [Integer]
> base10 n = if n <= 0
>   then []
>   else (n`rem`10) : base10 (n`quot`10)

```

Note that our lists of digits come out "backward"; that is, least significant first.

```haskell
$> base10 12345
[5,4,3,2,1]
```

Then we can detect whether a given number is a palindrome in base 10.

```haskell

> is_palindrome_10 :: Integer -> Bool
> is_palindrome_10 n = let ds = base10 n in
>   ds == (reverse ds)

```

Now we're not just looking for the largest palindrome of a given length; that would be easy -- the string of all 9s is the largest palindrome with a given number of digits. Instead, we want the largest palindrome that is the product of two 3-digit numbers. The most obvious solution is to list all the products of two 3-digit numbers, filter for the palindromes, and find the max.

```haskell

> -- the pair (a,b) which yields the largest
> -- palindrome product among the pairs of
> -- t-digit numbers
> pe4' :: Integer -> (Integer, Integer)
> pe4' t =
>   maximumBy (\(a,b) (c,d) -> compare (a*b) (c*d)) $
>   filter (is_palindrome_10 . uncurry (*)) $ 
>   [(a,b) | a <- [(10^(t-1))..(10^t - 1)], b <- [a..(10^t - 1)]]

```

This ``pe4'`` works well enough:

```haskell
$> pe4' 1
(3,3)
$> pe4' 2
(99,91)
$> pe4' 3
(993,913)
$> pe4' 4
(9901,9999)
```

Two observations. First, there appears to be a pattern emerging in these results. Second, unfortunately I can't feasibly explore that pattern further (yet) because as ``t`` gets larger, ``pe4' t`` gets way slow. It's not hard to see why; ``pe4' t`` constructs a list of $$\binom{9 \cdot 10^{t-1}}{2} = \frac{(9 \cdot 10^{t-1})(9 \cdot 10^{t-1} - 1)}{2}$$ candidates to check by brute force.

To see if we can find a better way, let's look at the simplest version of this problem: finding the largest palindrome product among products of 1-digit numbers. To this end, consider the multiplication table for 1-digit numbers below.

$$\begin{array}{c|ccccccccc}
  &  9 &  8 &  7 &  6 &  5 &  4 &  3 &  2 &  1 \\ \hline
9 & 81 & 72 & 63 & 54 & 45 & 36 & 27 & 18 &  9 \\
8 &    & 64 & 56 & 48 & 40 & 32 & 24 & 16 &  8 \\
7 &    &    & 49 & 42 & 35 & 28 & 21 & 14 &  7 \\
6 &    &    &    & 36 & 30 & 24 & 18 & 12 &  6 \\
5 &    &    &    &    & 25 & 20 & 15 & 10 &  5 \\
4 &    &    &    &    &    & 16 & 12 &  8 &  4 \\
3 &    &    &    &    &    &    &  9 &  6 &  3 \\
2 &    &    &    &    &    &    &    &  4 &  2 \\
1 &    &    &    &    &    &    &    &    &  1 \\
\end{array}$$

The first thing to jump out at me is that the vast majority of these products are *not* palindromes. That's not really surprising I guess -- there are $9 \cdot 10^{2t-1}$ different $2t$-digit numbers, but only $10^t$ of them are palindromes, so to a first approximation the probability that an arbitrary $2t$-digit number is a palindrome is about $10^{-t}$.

So maybe instead of searching among the products of $t$-digit numbers for palindromes, it would be faster to search among the palindromes for products of $t$-digit numbers.

But first, the rarity of palindromes highlights a disturbing possibility. The problem of finding the *largest* palindrome product implicitly assumes that at least one palindrome product must exist, but this is not obvious to me. But after some experimenting, I am convinced that palindrome products exist among pairs of $t$-digit numbers for any $t$; here is my constructive proof.

<div class="result">
<div class="thm">
Let $k \geq 2$ be even. Then there exist two $k$-digit numbers $A$ and $B$ such that $AB$ is a palindrome in base 10 having $2k$ digits.
</div>

<div class="proof">
Given a positive natural number $t$, we define $Q_t = \sum_{k=0}^{t-1} 100^k$. Then define $$A_t = 11Q_t, \quad\quad B_t = 90Q_t + 1,$$ and $$C_t = Q_t + 10 \cdot 100^t Q_t.$$ First note that $A_t$ and $B_t$ each have $2t$ digits, and that $C_t$ has $4t$ digits and is a palindrome. To see why, think of $C_t$ as numbers in base 100. I claim that $A_t B_t = C_t$ for all $t \geq 1$; we'll show this by induction on $t$.

For the base case we have $A_1 \cdot B_1 = (11)(91) = 1001 = C_1$.

For the inductive step, suppose $A_tB_t = C_t$ for some $t \geq 1$. Note that $Q_{t+1} = 1 + 100Q_t$ and $Q_{t+1} = Q_t + 100^t$. Now

$$\begin{eqnarray*}
A_{t+1}B_{t+1}
 & = & (11Q_{t+1})(90Q_{t+1} + 1) \\
 & = & (11Q_t + (11)100^t)(90Q_t + (90)100^t + 1) \\
 & = & (A_t + (11)100^t)(B_t + (90)100^t) \\
 & = & A_tB_t + (90)100^t A_t + (11)100^t B_t + (990)100^{2t} \\
 & = & C_t + (990)100^t Q_t + (990)100^t Q_t + (11)100^t + (990)100^{2t} \\
 & = & Q_t + (10)100^t Q_t + (990)100^t Q_t + (990)100^t Q_t + (11)100^t + (990)100^{2t} \\
 & = & (Q_t + 100^t) + (10)100^t(Q_t + 99Q_t + 99Q_t + 1 + (99)100^t) \\
 & = & Q_{t+1} + (10)100^t(100Q_t + 1 + (99)(Q_t + 100^t)) \\
 & = & Q_{t+1} + (10)100^t(Q_{t+1} + 99Q_{t+1}) \\
 & = & Q_{t+1} + (10)100^{t+1}Q_{t+1} \\
 & = & C_{t+1}
\end{eqnarray*}$$
</div>
</div>

<div class="result">
<div class="thm">
Let $A$ and $B$ be $d$-digit numbers (base 10) such that $AB$ is a $2d$-digit palindrome base 10. Now for positive integer $t$, define $$H_t = A(1 + 10^{d+t})\ \mathrm{and}\ K_t = B(1 + 10^{d+t}).$$ Then $H_t$ and $K_t$ are $(2d+t)$-digit numbers and $H_tK_t$ is a $(4d+2t)$-digit palindrome.
</div>

<div class="proof">

</div>
</div>
