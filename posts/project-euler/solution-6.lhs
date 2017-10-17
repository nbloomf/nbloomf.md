---
title: Project Euler #6: Sum Square Difference
author: nbloomf
date: 2017-03-11
tags: project-euler, literate-haskell
---

First some boilerplate.

> module ProjectEuler006 where
> 
> import System.Exit

[Problem 6](https://projecteuler.net/problem=6) from Project Euler:

<div class="problem">
The sum of the squares of the first ten natural numbers is $$1^2 + 2^2 + ... + 10^2 = 385.$$

The square of the sum of the first ten natural numbers is $$(1 + 2 + ... + 10)^2 = 55^2 = 3025.$$

Hence the difference between the sum of the squares of the first ten natural numbers and the square of the sum is 3025 − 385 = 2640.

Find the difference between the sum of the squares of the first one hundred natural numbers and the square of the sum.
</div>

We'll start with the obvious thing:

> sum_squares' :: Integer -> Integer
> sum_squares' n = sum $ map (^2) [1..n]
> 
> square_sum' :: Integer -> Integer
> square_sum' n = (^2) $ sum [1..n]
>
> pe6' :: Integer -> Integer
> pe6' n = (square_sum' n) - (sum_squares' n)

Sanity check:

```haskell
$> sum_squares' 10
385
$> square_sum' 10
3025
$> pe6' 10
2640
```

woo

If it's worth doing, it's worth overdoing.

In big sigma notation, what we're looking for is this: $$\left(\sum_{k=1}^n k\right)^2 + \sum_{k=1}^n k^2.$$

One optimization we could try is to traverse the list ``[1..n]`` only once instead of twice. Say, traverse the list and keep track of the sums of both first and second powers at the same time, then square and subtract. In principle that should take half the time.

But wait! 

I recognize that first sum; it represents the $n$th [triangular number](https://en.wikipedia.org/wiki/Triangular_number), $T(n)$. I also happen to remember that there is a closed form expression for $T(n)$ in terms of $n$ -- specifically, $$T(n) = \frac{n(n+1)}{2}.$$

If we had a closed form for the second sum, the sum of the first $n$ squares, we could solve this problem without traversing a list at all.

I vaguely remember that there is indeed a closed form formula for $\sum k^2$. But I can never remember exactly what it is! And I don't feel like looking it up. So let's see if we can find it bare-handed.

The expression $$\sum k^2$$ reminds me of the left hand side of $$\int x^2 = \frac{1}{3}x^3 + C.$$ It seems reasonable to hope that $\sum k^2$ would be a degree 3 polynomial of $n$, so let's assume that it is.

More precisely, suppose $$\sum_{k=0}^n k^2 = S(n) = an^3 + bn^2 + cn + d$$ for some rational numbers $a$, $b$, $c$, and $d$.

Note that 

$$\begin{eqnarray*}
\sum_{k=0}^0 k^2 = 0^2 & = & 0 \\
\sum_{k=0}^1 k^2 = 0^2 + 1^2 & = & 1 \\
\sum_{k=0}^2 k^2 = 0^2 + 1^2 + 2^2 & = & 5 \\
\sum_{k=0}^3 k^2 = 0^2 + 1^2 + 2^2 + 3^2 & = & 14 \\
\end{eqnarray*}$$

This means that whatever the coefficients of $S$ are, we have $S(0) = 0$, $S(1) = 1$, $S(2) = 5$, and $S(3) = 14$. Expanding $S$ with these arguments gives a system of equations:

$$\begin{array}{rcrcrcrcl}
    &   &    &   &    &   & d & = & 0  \\
  a & + &  b & + &  c & + & d & = & 1  \\
 8a & + & 4b & + & 2c & + & d & = & 5  \\
27a & + & 9b & + & 3c & + & d & = & 14 \\
\end{array}$$

Since clearly $d = 0$, this simplifies to the following augmented matrix.

$$\left[\begin{array}{ccc|c}
1  & 1 & 1 & 1  \\
8  & 4 & 2 & 5  \\
27 & 9 & 3 & 14 \\
\end{array}\right]$$

[WolframAlpha](http://www.wolframalpha.com/input/?i=row+reduce+[[1,1,1,1],[8,4,2,5],[27,9,3,14]]) says that matrix is row equivalent to this one:

$$\left[\begin{array}{ccc|c}
1 & 0 & 0 & 1/3 \\
0 & 1 & 0 & 1/2 \\
0 & 0 & 1 & 1/6 \\
\end{array}\right]$$

Which (if true) gives $$S(n) = \frac{1}{3} n^3 + \frac{1}{2} n^2 + \frac{1}{6} n = \frac{n(n+1)(2n+1)}{6}.$$

But we don't have to take WolframAlpha's word for it. We can verify that this expression matches $\sum_{k=1}^n k^2$ for all $n$ by induction. In the base case $n = 1$, we have $$\sum_{k=1}^1 k^2 = 1^2 = 1 = S(1).$$ And if the expressions match for some $n \geq 1$, we have

$$\begin{eqnarray*}
\sum_{k=1}^{n+1} k^2
 & = & \sum_{k=1}^n k^2 + (n+1)^2 \\
 & = & \frac{n(n+1)(2n+1)}{6} + (n+1)^2 \\
 & = & \frac{n(n+1)(2n+1) + 6(n+1)^2}{6} \\
 & = & \frac{(n+1)(n+2)(2(n+1)+1)}{6}
\end{eqnarray*}$$

as needed. Which means that $$T(n) + S(n) = \frac{n(n+1)(n-1)(3n+2)}{12}.$$

Let's try it.

> pe6'' :: Integer -> Integer
> pe6'' n = n*(n+1)*(n-1)*(3*n+2) `quot` 12
>
> test_sum_square :: Integer -> Bool
> test_sum_square n = (pe6' n) == (pe6'' n)

Check:

```haskell
$> all test_sum_square [1..1000]
True
```

Some timing info to compare:

------------------------------------------
``k``  ``pe6' (10^k)``  ``pe6'' (10^k)``
------ ---------------- -----------------
4      0.08 s           0.01 s

5      0.30 s           0.01 s

6      2.87 s           0.01 s

7      31.20 s          0.01 s

8      choked!          0.01 s

100    you're kidding   0.02 s

1000   mmm hmm          0.05 s
------------------------------------------

(This is the difference between $n$ and $\log(n)$.)

So the answer is:

> pe6 :: Integer
> pe6 = pe6'' 100
> 
> main :: IO ()
> main = do
>   let
>     success = and
>       [ all test_sum_square [1..1000]
>       ]
>   if success
>     then putStrLn $ show pe6
>     else exitFailure
