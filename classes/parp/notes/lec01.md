---
title: Notes on Lecture 1
---

([Go back to the course page](/classes/parp/index.html))

[youtube id='uJHgKrpuSZ0' show-related='no']

## Links

* [Slides](https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture01_intro_jwd16_4pp.pdf) ([archive](http://web.archive.org/web/20170119172347/https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture01_intro_jwd16_4pp.pdf))
* [Top500](https://www.top500.org/) -- Computer leaderboard
* [Parallel Programming Patterns: Mining HPC for the Desktop](http://www.drdobbs.com/go-parallel/article/print?articleId=212903308) ([archive](http://web.archive.org/web/20170119172500/http://www.drdobbs.com/go-parallel/article/print?articleId=212903308)) -- Article in Dr. Dobbs on design patterns for parallel programs; mentions Berkeley's 13 "Motifs"


## Principles of Parallel Computing

What makes it harder than sequential computing?

* **Finding enough parallelism** -- watch out for [Amdahl's Law](https://en.wikipedia.org/wiki/Amdahl's_law)
* **Granularity** of subtasks -- size of work units
* **Locality** -- moving data is more expensive than arithmetic
* **Load balancing** -- want all processors working all the time
* **Coordination and Synchronization** -- How to balance communication overhead, avoid race conditions, share memory
* **Performance modeling**, debugging, and tuning -- How to measure and improve performance

These concerns are not independent. For example, finer granularity requires more communication overhead but may improve load balancing.

No silver bullets -- but then that's what makes the problem hard.


## The 13 Dwarfs

Common underlying parallel strategies.

* Finite State Machines
* Combinatorial logic
* Graph traversal
* Structured grid
* Dense linear algebra
* Sparse linear algebra
* [FFT](https://en.wikipedia.org/wiki/Fast_Fourier_transform)
* Dynamic programming
* [N-body](https://en.wikipedia.org/wiki/N-body_simulation) (and maybe [Navier-Stokes?](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_equations))
* MapReduce
* Backtrack, Branch & Bound
* Graphical models
* Unstructured grid

Idea: instead of asking what **strategies** can solve a given **problem**, ask what **problems** a given **strategy** can solve. E.g. parallel computers are really good at FFT, so can a given problem be encoded as an FFT problem?
