---
title: Notes on Lecture 2
---

([Go back to the course page](/classes/parp/index.html))

[youtube id='dr1tDPfXchk' show-related='no']

## Links

* [Slides](https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture02_memhier_jwd16_4pp.pdf) ([archive](http://web.archive.org/save/_embed/https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture02_memhier_jwd16_4pp.pdf))

## Single Processor Machines

"Most programs run at &lt;10% efficiency on a single machine" (source?) so there may well be a 10x speedup to be had by focusing on sequential code, before doing the hard stuff.

Some considerations:

* **Memory hierarchy**: In principle, the processor has some named memory cells (registers) and an address space, and instructions look like "load address X into register A, increment register A, write register A to address X". In practice, read/write times can be wildly different (cache) depending on **spatial and temporal locality of memory accesses** because physics.
* **On-die parallelism**: A single processor may have different "functional units" that can run at the same time (improving efficiency) depending on the **order of the instructions**.
* **Pipelining**: The laundromat example. Each instruction (regardless of order) must be decoded, have arguments fetched, etc., which can be done in stages, like an assembly line, to improve throughput. To maintain max efficiency instructions at different stages should not step on each other, watch for [pipeline stalls](https://en.wikipedia.org/wiki/Bubble_%28computing%29).

Compilers should abstract these details away, but aren't completely there yet.

## Simplified memory model

Suppose we run a program that accesses fast memory (cost 0) and slow memory and does arithmetic (cost &gt;0). Let

* $m$ be the number of words moved between fast & slow memory
* $t_m$ be the time per slow memory access
* $f$ be the number of arithmetic operations
* $t_f$ be the time per arithmetic operation
* $q = f/m$ the # of flops per slow memory access -- called **computational intensity**

If all data fits in fast memory, then the time taken is $ft_f$. (Lower bound)

If we have to use slow memory, then time taken is $$ft_f + mt_m = ft_f\left(1 + \frac{t_m}{t_f} \cdot \frac{1}{q}\right)$$

* $t_m/t_f$: Called **machine balance** -- we have no control over this.

Key insight: with $f$ fixed (typically by the algorithm) rearranging the computation to minimize $m$ is the only way to improve intensity.
