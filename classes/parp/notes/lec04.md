---
title: Notes on Lecture 4
---

([Go back to the course page](/classes/parp/index.html))

[youtube id='JS52IuQ-UEg' show-related='no']

## Links

* [Slides](https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture04_sources1_jwd16_4pp.pdf) ([archive](http://web.archive.org/save/_embed/https://people.eecs.berkeley.edu/~demmel/cs267_Spr16/Lectures/lecture04_sources1_jwd16_4pp.pdf))

## Machine Model 1a: Shared Memory

* Multiple procs with local cache and shared cache & memory via a bus
* Scaling problems: cache coherence, memory bus.
* Nice for programming, bad for hardware

## Machine Model 1b: Multithreaded Processor

* Shared cache & memory
* Each proc switches threads (contexts) instead of idling
* Doesn't solve coherence problems, but keeps CPUs busy

## Machine Model 1c: Distributed Shared Memory

* Local cache and physically distributed shared memory
* Still has coherence issues
* <=512 procs is limit

Shared memory is a nice programming model, so effort is put into mapping to other hardware models.

## Message Passing: 

* All procs are running the same program, take an ID number as a parameter
* All data is local; data shared via send/receive calls.
* [MPI](http://mpi-forum.org/): The Standard
* Semantics of send/receive: telephone vs. post office (blocking vs. nonblocking)
* Proc with local cache & memory, + NIC

## Machine Model 2b: Internet/Grid Computing

* Like 2, but over an untrusted network
* Trust protocols important
* BOINC, @Home

## Programming Model 2a: Global Address Space

* Illusion of shared memory
* Languages: UPC, Titanium, Co-Array Fortran

## Machine Model 2c: Global Address Space

## Programming Model 3: Data Parallel

* SIMD
* CUDA, OpenCL
* No race conditions; parallelism is "atomic"
* GPUs
* Drawback: not all problems fit this model

## Machine Model 3a: SIMD

* All procs carry out the same program

## Machine Model 3b: Vector Machines

* Expensive

## Machine Model 4: Hybrid

* Hierarchy or heterogeneous

Goal for all: Divide work into parts that are

* mostly independent (little synchronization)
* about the same size (load balancing)
* have good locality (little communication)

## Sources of Parallelism and Locality in Simulations

Basic kinds of simulations

* $\mathbb{N} \rightarrow \mathbb{N}$ Discrete event systems: Life, manufacturing systems, finance, ...
* $\mathbb{N} \rightarrow \mathbb{R}$ Particle systems: billiard balls, galaxies, atoms, ...
* $\mathbb{R} \rightarrow \mathbb{N}$ Lumped variable depending on continuous parameters: ODEs, Differential algebraic equations, finite element models, ...
* $\mathbb{R} \rightarrow \mathbb{R}$ Continuous variables depending on continuous parameters: PDEs, heat, elasticity, finance (Black-Scholes) ...

A given phenomenon can be simulated at different levels. What are the primitives? What do we treat as a black box?

## Sharks and Fish

Discrete Event Simulations (both time and space are discrete)

* Decompose domain
    * Minimizing "surface to volume". In general, graph partitioning.
* Run each component ahead, either
    * Synchronously (communicate at each time step)
    * Asynchronously (communicate only on demand)
        * Conservatively: wait for input (need deadlock detection)
        * Speculatively: assume no input (need to be able to roll back)
