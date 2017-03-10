---
title: Project Euler Solution #4: Largest Palindrome Product
author: nbloomf
date: 2017-03-08
tags: project-euler
---

This post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-03-08-project-euler-solution-4.lhs) into GHCi and play along.

```haskell

> import Data.List
> import Data.Maybe

```

[Problem 4](https://projecteuler.net/problem=4) from Project Euler:

<div class="problem">

A palindromic number reads the same both ways. The largest palindrome made from the product of two 2-digit numbers is 9009 = 91 × 99.

Find the largest palindrome made from the product of two 3-digit numbers.
</div>

"Palindromeness" is very different from most interesting properties of numbers; it is an artifact of one of many possible *representations* of the number. In this case, the representation in base 10.

Let's start by nailing down a definition for "palindrome".

<div class="result">
<div class="defn">
Suppose $A = \sum_{k=0}^{t-1} a_k 10^k$ is a $t$-digit number base 10 (that is, the $a_k$ are integers between 0 and 9 (inclusive) and $a_{t-1}$ is not zero). We say $A$ is a *palindrome* if $a_{t-1-k} = a_k$ for all $0 \leq k < t$.
</div>
</div>

The first thing I'll do is write helper functions to convert a number to its base 10 digits and back.

```haskell

> -- base 10 digits of n in 'little endian' order
> -- (least significant digits first)
> toDigits :: Integer -> [Integer]
> toDigits n = if n <= 0
>   then []
>   else (n`rem`10) : toDigits (n`quot`10)
> 
> fromDigits :: [Integer] -> Integer
> fromDigits = sum . zipWith (*) (map (10^) [0..])
> 
> numDigits :: Integer -> Integer
> numDigits n = sum $ map (const 1) $ toDigits n

```

Sanity check:

```haskell

> test_digits :: Integer -> Bool
> test_digits n = n == (fromDigits $ toDigits n)

$> all test_digits [1..1000000]
True

```

Note that our lists of digits come out "backward"; that is, least significant first.

```haskell
$> toDigits 12345
[5,4,3,2,1]
```

Then we can detect whether a given number is a palindrome in base 10.

```haskell

> is_palindrome_10 :: Integer -> Bool
> is_palindrome_10 n = let ds = toDigits n in
>   ds == (reverse ds)

```

Now we're not just looking for the largest palindrome of a given length; that would be easy -- the string of all 9s is the largest palindrome with a given number of digits. Instead, we want the largest palindrome that is the product of two 3-digit numbers. The most obvious solution is to list all the products of two 3-digit numbers, filter for the palindromes, and find the max.

```haskell

> -- the triple (a,b,a*b) which yields the largest
> -- palindrome product a*b among the pairs of
> -- t-digit numbers a and b
> pe4' :: Integer -> (Integer, Integer, Integer)
> pe4' t =
>   let
>     thd (_,_,x) = x
>     min = 10^(t-1)
>     max = 10^t - 1
>   in
>     maximumBy (\x y -> compare (thd x) (thd y)) $
>     filter (is_palindrome_10 . thd) $ 
>     [(a,b,a*b) | a <- [min..max], b <- [a..max]]

```

This ``pe4'`` works well enough:

```haskell
$> pe4' 1
(3,3,9)
$> pe4' 2
(99,91,9009)
$> pe4' 3
(993,913,906609)
$> pe4' 4
(9901,9999,99000099)
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

The first thing to jump out at me is that the vast majority of these products are *not* palindromes. That's not really surprising I guess -- there are $9 \cdot 10^{2t-1}$ different $2t$-digit numbers, but only $9 \cdot 10^{t-1}$ of them are palindromes, so to a first approximation the probability that an arbitrary $2t$-digit number is a palindrome is about $10^{-t}$.

So maybe instead of searching among the products of $t$-digit numbers for palindromes, it would be faster to search among the palindromes for products of $t$-digit numbers.

A Digression on Palindromes
---------------------------

The rarity of palindromes highlights a disturbing possibility. The problem of finding the *largest* palindrome product implicitly assumes that at least one palindrome product must exist, but this is not obvious to me. After some experimenting, I am convinced that palindrome products exist among pairs of $t$-digit numbers for any $t$. I got a little distracted thinking about this probem, so I'll just dump the results here.

The first result allows us to recognize a family of palindromes constructed from other palindromes.

<div class="result">
<div class="thm">
Let $t,u,v \geq 1$ be natural numbers, and let $A = \sum_{k=0}^{t-1} a_k 10^k$ and $B = \sum_{k=0}^{u-1} b_k 10^k$ be $t$- and $u$-digit palindromes, respectively. That is, $a_k = a_{t-1-k}$ when $0 \leq k < t$ and $b_k = b_{u-1-k}$ when $0 \leq k < u$. Then $$M = A + 10^{t+v} B + 10^{t+u+2v} A$$ is a $(2t+u+2v)$-digit palindrome.
</div>

<div class="proof">
Note that

$$\begin{eqnarray*}
M
 & = & A + 10^{t+v} B + 10^{2t+u+2v} A \\
 & = & \sum_{k=0}^{t-1} a_k 10^k + 10^{t+v} \sum_{k=0}^{u-1} b_k 10^k + 10^{2t+u+2v} \sum_{k=0}^{t-1} a_k 10^k \\
 & = & \sum_{k=0}^{t-1} a_k 10^k + \sum_{k=0}^{u-1} b_k 10^{t+v+k} + \sum_{k=0}^{t-1} a_k 10^{t+u+2v+k} \\
 & = & \sum_{k=0}^{t-1} a_k 10^k + \sum_{k=t+v}^{t+u+v-1} b_{k-t-v} 10^k + \sum_{k=t+u+2v}^{2t+u+2v-1} a_{k-t-u-2v} 10^k \\
 & = & \sum_{k=0}^{2t+u+2v-1} e_k 10^k
\end{eqnarray*}$$

where

$$e_k = \left\{ \begin{array}{ll} a_k & \mathrm{if}\ 0 \leq k < t \\ 0 & \mathrm{if}\ t \leq k < t+v \\ b_{k-t-v} & \mathrm{if}\ t+v \leq k < t+u+v \\ 0 & \mathrm{if}\ t+u+v \leq k < t+u+2v \\ a_{k-t-u-2v} & \mathrm{if}\ t+u+2v \leq k < 2t+u+2v. \end{array} \right.$$

Certainly $M$ has $2t+u+2v$ digits. To see that $M$ is a palindrome, we need to check that $$e_{2t+u+2v-1-k} = e_k$$ for $0 \leq k < 2t+u+2v$. We will break this interval into 5 subintervals.

1. Suppose $0 \leq k < t$. Then $0 \leq t-1-k < t$, and so $t+u+2v \leq 2t+u+2v-1-k < 2t+u+2v$. So $$e_{2t+u+2v-1-k} = a_{2t+u+2v-1-k-t-u-2v} = a_{t-1-k} = a_k = e_k.$$
2. Suppose $t \leq k < t+v$. Then $0 \leq t+v-1-k < v$, and so $t+u+v \leq 2t+u+2v-1-k < t+u+2v$. So $$e_{2t+u+2v-1-k} = 0 = e_k.$$
3. Suppose $t+v \leq k < t+u+v$. Then $0 \leq t+u+v-1-k < u$, and so $t+v \leq 2t+u+2v-1-k < t+u+v$. So $$\begin{eqnarray*} e_{2t+u+2v-1-k} & = & b_{2t+u+2v-1-k-t-v} \\ & = & b_{t+u+v-1-k} \\ & = & b_{u-1-t-u-v+1-k} \\ & = & b_{k-t-v} \\ & = & e_{k}. \end{eqnarray*}$$
4. Suppose $t+u+v \leq k < t+u+2v$. Then $0 \leq t+u+2v-1-k < v$, and so $t \leq 2t+u+2v-1-k < t+v$. So $$e_{2t+u+2v-1-k} = 0 = e_k.$$
5. Suppose $t+u+2v \leq k < 2t+u+2v$. Then $0 \leq 2t+u+2v-1-k < t$. So $$\begin{eqnarray*} e_{2t+u+2v-1-k} & = & a_{2t+u+2v-1-k} \\ & = & a_{t-1-2t-u-2v+i+k} \\ & = & a_{k+t-u-2v} \\ & = & e_k. \end{eqnarray*}$$

Thus $M$ is a $(2t+u+2v)$-digit palindrome.
</div>
</div>

This result lets us recognize *some* palindromes.

The next result lets us construct new palindrome products from old ones.

<div class="result">
<div class="thm">
Let $A$ and $B$ be $t$-digit numbers such that both $AB$ and $2AB$ are $2t$-digit palindromes. Let $v$ be a positive integer, and define $$H_v(A) = A(1 + 10^{2t+v})\ \mathrm{and}\ K_v(B) = B(1 + 10^{2t+v}).$$ Then $H_v$ and $K_v$ are $(3t+v)$-digit numbers and $H_vK_v$ is a $(6t+2v)$-digit palindrome.
</div>

<div class="proof">
Expanding $H_vK_v$, we have $$H_vK_v = AB + 10^{2t+v}(2AB) + 10^{2t+2t+2v}AB.$$ The previous theorem applies, and $H_vK_v$ is a $(6t+2v)$-digit palindrome.
</div>
</div>

Let's make $H_v$ and $K_v$ executable.

```haskell

> h_ :: Integer -> Integer -> Integer
> h_ v a = a * (1 + 10^(2*t+v))
>   where t = numDigits a
> 
> k_ :: Integer -> Integer -> Integer
> k_ v b = b * (1 + 10^(2*t+v))
>   where t = numDigits b

```

And the next result gives us a concrete family of palindrome products with factors of even digit length.

<div class="result">
<div class="thm">
Let $t$ and $m$ be positive natural numbers, and define $Q_{t,m} = \sum_{k=0}^{t-1} 10^{mk}$. Now define $$A_{t,m} = Q_{2t,m},$$ $$B_{t,m} = 1 + 10^{tm}(10^m-1)Q_{t,m},$$ and $$C_t = Q_{t,m}(1 + 10^{3tm}).$$

Then $A_t$ is a $(2tm - m + 1)$-digit number, and $B_t$ is a $2tm$-digit number, and both $A_tB_t$ and $2A_tB_t$ are $(4tm - m + 1)$-digit palindromes.
</div>

<div class="proof">
Note that $A_{t,m} = Q_{t,m}(1 + 10^{tm})$ and $$Q_{t,m} = \frac{10^{tm} - 1}{10^m-1}.$$ Expanding $A_{t,m}B_{t,m}$, then, we have $$A_{t,m}B_{t,m} = Q_{t,m}(1 + 10^{tm})(1 - 10^{tm} + 10^{2tm}) = C_{t,m}$$ as needed.

To see the digit counts, note that $Q_{t,m}$ has $(tm-m+1)$ digits. Note also that all the digits of $C_{t,m}$ are 1, so that $2C_{t,m}$ is also a palindrome.
</div>
</div>

Let's make $Q_{t,m}$, $A_{t,m}$, and $B_{t,m}$ executable.

```haskell

> q_ :: Integer -> Integer -> Integer
> q_ t m = sum $ map (\k -> 10^(m*k)) [0..(t-1)]
> 
> a_ :: Integer -> Integer -> Integer
> a_ t m = q_ (2*t) m
> 
> b_ :: Integer -> Integer -> Integer
> b_ t m = 1 + (10^(t*m))*(10^m - 1)*(q_ t m)
> 
> c_ :: Integer -> Integer -> Integer
> c_ t m = (q_ t m)*(1 + 10^(3*t*m))

```

Sanity check:

```haskell

> test_abc :: Integer -> Integer -> Bool
> test_abc t m =
>   let
>     a = a_ t m; b = b_ t m; c = c_ t m
>   in and
>     [ a*b == c
>     , (numDigits a) == 2*t*m - m + 1
>     , (numDigits b) == 2*t*m
>     , (numDigits c) == 4*t*m - m + 1
>     , is_palindrome_10 c
>     , is_palindrome_10 (2*c)
>     ]

```

And a test:

```haskell

$> and [test_abc t m | t <- [1..10], m <- [1..10]]
True

```

This gives an infinite family of palindrome products. Note that if $m = 1$, then both factors have the same number of digits -- $2t$ -- and the product has $4t$ digits.

Here are the first 5 examples.

--------------------------------------------------
$t$  $A_{t,m}$   $B_{t,m}$   $A_{t,m}B_{t,m}$
---- ----------  ---------   -----------------
1    11          91          1001

2    1111        9901        11000011

3    111111      999001      111000000111

4    11111111    99990001    1111000000001111

5    1111111111  9999900001  11111000000000011111
--------------------------------------------------

Note that row $k$ in this table has factors $A$ and $B$ with $2k$ digits, and the (palindrome) product has $4k$ digits.

Taking the first row, $A = 11$ and $B = 91$, we can use these in our $H_v$ and $K_v$, with $v = 1$, we get another family of palindrome products.

-----------------------------------------------------------------
$v$  $H_v(A_{1,1})$  $K_v(B_{1,1})$  $H_v(A_{1,1})K_v(B_{1,1})$
---- --------------- --------------- ---------------------------
1    1100011         9100091         10010200201001

3    110000011       910000091       100100020020001001

5    11000000011     91000000091     1001000002002000001001

7    1100000000011   9100000000091   10010000000200200000001001
-----------------------------------------------------------------

Note that if $v = 2k+1$ then this table gives two $(2k+7)$-digit numbers whose (palindrome) product has $4k+14$ digits.

Along with the observation that $993 \cdot 913 = 906609$ and $11011 \cdot 91091 = 1003003001$, we can say the following.

<div class="result">
<div class="thm">
Let $k \geq 2$. Then among the $k$-digit numbers, there exists a pair $A$ and $B$ such that $AB$ is a $2k$-digit palindrome.

In particular, the largest such palindrome has $2k$ digits.
</div>
</div>

Right, because the whole point of this digression was to establish this fact about largest palindrome products.

Meanwhile
---------

Our alternate strategy for this problem was to search among the palindromes for $k$-digit factorizations; and now we know that it's enough to look among the $2k$-digit palindromes -- we are guaranteed to find a factorization there. This simplifies the search space a bit.

So the new strategy is to generate the $2k$-digit palindromes in reverse order and look for the first one that factors are a product of two $k$-digit numbers.

```haskell

> -- the 2k-digit palindromes
> palindromes :: Integer -> [Integer]
> palindromes k = map (fromDigits . make) (digits k)
>   where
>     -- turn a list into a palindrome
>     make ds = ds ++ reverse ds
> 
>     digits :: Integer -> [[Integer]]
>     digits k = foo k []
>       where
>         foo 0 _ = [[]]
>         foo k z = do
>           d  <- [9,8,7,6,5,4,3,2,1] ++ z
>           ds <- foo (k-1) [0]
>           return (d:ds)

```

Now given a $2k$-digit palindrome, we want to know whether it factors as a product of two $k$-digit numbers. Note that if $N = AB$, then without loss of generality $A \leq \sqrt{N}$ and $\sqrt{N} \leq B$. So it is enough to search for a factorization of $N$ where $10^{t-1} \leq A \leq \lfloor \sqrt{N} \rfloor$.

Here's a utility function to find $\lfloor \sqrt{N} \rfloor$ by bisection.

```haskell

> -- find t such that t^2 <= n < (t+1)^2
> floor_sqrt :: Integer -> Integer
> floor_sqrt n =
>   let
>     bisect (a,b) = if b-a <= 1
>       then a
>       else let m = (b+a)`quot`2 in
>         if m^2 <= n
>           then bisect (m,b)
>           else bisect (a,m)
>   in
>     if n < 0
>       then error "floor_sqrt: negative argument"
>       else bisect (1,n)

```

Sanity check:

```haskell

> test_floor_sqrt :: Integer -> Bool
> test_floor_sqrt n = let q = floor_sqrt n in
>   (q^2 <= n) && (n < (q+1)^2)

```

And a test:

```haskell
%> all test_floor_sqrt [1..10000]
True
```

Also, if we wish to factor a $2k$-digit number as a product of $k$ digit numbers, we should search "down" from $\lfloor \sqrt{N} \rfloor$ to $10^{t-1}$ rather than the reverse. This is because smaller factors are likely to give quotients with too many digits.

```haskell

> -- search for a factorization of n into t-digit factors
> does_factor :: Integer -> Integer -> Maybe (Integer, Integer)
> does_factor t n =
>   let
>     check m
>       | m < 10^(t-1) = Nothing
>       | n`rem`m == 0 = if numDigits (n`quot`m) == t
>           then Just m
>           else check (m-1)
>       | otherwise = check (m-1)
>   in
>     case check (floor_sqrt n) of
>       Nothing -> Nothing
>       Just m  -> Just (m, n`quot`m)
>
> pe4'' :: Integer -> (Integer, Integer, Integer)
> pe4'' k =
>   let
>     (a,b) = head $ catMaybes $ map (does_factor k) (palindromes k)
>   in (a,b,a*b)

```

This ``pe4''`` is still slow, as we still check an exponential number of cases. But we can squeeze out a couple more values.

```haskell
$> pe4'' 2
(91,99,9009)
$> pe4'' 3
(913,993,906609)
$> pe4'' 4
(9901,9999,99000099)
$> pe4'' 5
(99681,99979,9966006699)
```

Interesting! It looks like the form of the largest palindrome product depends on whether the factors have an even or odd number of digits.

Anyway, the final answer is:

```haskell

> pe4 :: Integer
> pe4 = let (_,_,x) = pe4'' 3 in x

```
