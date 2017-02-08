---
title: Notes on Lecture 5
---

([Go back to the course page](/classes/parp/index.html))

[youtube id='xfWIhmfiaRk' show-related='no']

## Links

* [Slides](https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture05_sources2_jwd16_4pp.pdf) ([archive](http://web.archive.org/save/_embed/https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture05_sources2_jwd16_4pp.pdf))
* [Quadtrees](https://en.wikipedia.org/wiki/Quadtree)
* The classification of [2nd order linear PDEs](https://en.wikipedia.org/wiki/Partial_differential_equation#Linear_equations_of_second_order)

Vocab: "reduction" refers to a computation of the form $$a_1 \oplus a_2 \oplus \cdots \oplus a_n,$$ where $\oplus$ is an associative binary operation -- that is, a function of two variables such that $x \oplus (y \oplus z) = (x \oplus y) \oplus z$. Basic numeric examples of such $\oplus$ include addition, multiplication, max, min, and gcd. It turns out that more exotic and useful examples are common. Such computations parallelize very nicely, because they can be "parenthesized" however we want.

(Full disclosure: the algebraic structure we get from $\oplus$ is called a [semigroup](https://en.wikipedia.org/wiki/Semigroup); my dissertation involved semigroups.)
