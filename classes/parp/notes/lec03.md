---
title: Notes on Lecture 3
---

([Go back to the course page](/classes/parp/index.html))

[youtube id='yJ9-Y-T5V7Y' show-related='no' class='video-container']

## Links

* [Slides](https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture03_machines_jwd16_4pp.pdf) ([archive](http://web.archive.org/save/_embed/https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture03_machines_jwd16_4pp.pdf))


## Matrix Multiplication (revisited)

A standard: [BLAS](http://www.netlib.org/blas/) (Basic Linear Algebra Subprograms). Machine-independent API for linear algebra.

Why?

* Correctness -- floating point is complicated, so BLAS hides details.
* Efficiency -- take advantage of vectorizable operations.

The schoolbook algorithm for matrix multiplication takes $O(n^3)$ arithmetic operations, but there are asymptotically better algorithms.

* [Strassen's algorithm](https://en.wikipedia.org/wiki/Strassen_algorithm) uses $O(n^{2.8074})$ and is useful in practice (though banned by Top500!)
* The [Coppersmith-Winograd algorithm](https://en.wikipedia.org/wiki/Coppersmith%E2%80%93Winograd_algorithm) uses $O(n^{2.375})$, but constants make it impractical on practically-sized matrices.
* [Group-theoretic algorithms for matrix multiplication](https://arxiv.org/abs/math/0511460) by Cohn, Kleinsberg, Szegedy, Umans (2003); gives a $O(n^{2.41})$ points the way to an $O(n^2)$ algorithm, but some hard algebra is required.

For recursive matrix multiplication algorithms, the layout of data in memory becomes vitally important. Example: Morton's [Z-order](https://en.wikipedia.org/wiki/Z-order_curve). A bijective map $\mathbb{N} \leftrightarrow \mathbb{N} \times \mathbb{N}$ which is good at preserving locality.


## Autotuning

Our algorithm may have some tunable parameters which will affect efficiency. (Example: [Cooley-Tukey FFT](https://en.wikipedia.org/wiki/Cooley%E2%80%93Tukey_FFT_algorithm).) But modern compilers also expose lots of options ([here](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html#Optimize-Options) is the list for GCC) for optimization, but this "optimalness" is not monotone.

**Important question**: Which combination of parameters and options results in the fastest program?

Autotuning answers this question by testing combinations automatically. The results will likely be machine-specific and program-specific.

We can help the compiler:

* Loop unrolling
* Use intermediate variables
* The ``register`` keyword

The more guarantees the compiler has about our program, the more aggressive it can be when optimizing. One area of research: strengthening the type system.


## Models

Ideally, we could write our programs however we want and the compiler will optimize them for our machine. In practice, we have to know something about the machine. There are 6 basic models, each of which has some standard libraries for common parallel patterns.

Models are tightly coupled to languages and libraries.

* **Shared memory**: Processors share physical memory. Does not scale well past ~32 processors.
* **Shared address space**: Processors share *logical* memory space, which is physically distributed, so that access time is nonuniform. E.g. memory addresses 0--15 are local to processor 0, 16--31 are local to processor 1, etc.
* **Message passing**: (MPI) Data must be shared by explicitly sending messages between processors. Tedious, but scales well.
* **Data parallel**: Vector operations; e.g. "Add this $n$-vector to this other $n$-vector" is $O(1)$. GPUs do this.
* **Clusters**: 
* **Grid**: A heterogeneous network of machines, each of which has its own internal architecture (SMPs, GPUs), maybe communicating over a very slow network. Good for [embarrassingly parallel](https://en.wikipedia.org/wiki/Embarrassingly_parallel) problems. Examples: [Folding@Home](https://folding.stanford.edu/), [GIMPS](http://www.mersenne.org/)


## Aside: Morton's Z-order

Morton's Z order maps a natural number $k$ to a pair of natural numbers $(u,v)$ using the base 4 expansion of $k$ and the base 2 expansions of $u$ and $v$. (Naturally generalizes to higher dimensional arrays.)

```haskell
-- Base b digits of a positive integer
-- (least significant first)
base :: Integer -> Integer -> [Integer]
base b k
  | b <= 1 = []
  | k <= 0 = []
  | otherwise = (rem k b) : base b (quot k b)


mapIndexToEntry :: Integer -> (Integer, Integer)
mapIndexToEntry k = foldr (.+) (0,0) $ map eps $ zip [0..] $ base 4 k
  where
    -- Pointwise sum
    (a1,a2) .+ (b1,b2) = (a1+b1, a2+b2)

    -- Offset vector
    eps (t,0) = (0,   0)
    eps (t,1) = (2^t, 0)
    eps (t,2) = (0,   2^t)
    eps (t,3) = (2^t, 2^t)


mapEntryToIndex :: (Integer, Integer) -> Integer
mapEntryToIndex (u,v) = sum $ map del $ zip [0..] $ pad (base 2 u) (base 2 v)
  where
    -- Like zip, but shorter list is padded with zero.
    pad []     ys     = map (\y -> (0,y)) ys
    pad xs     []     = map (\x -> (x,0)) xs
    pad (x:xs) (y:ys) = (x,y) : pad xs ys

    -- Offset index
    del (t,(0,0)) = 0 * 4^t
    del (t,(1,0)) = 1 * 4^t
    del (t,(0,1)) = 2 * 4^t
    del (t,(1,1)) = 3 * 4^t
```
