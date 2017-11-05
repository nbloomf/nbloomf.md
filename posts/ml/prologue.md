---
title: Prologue
author: nbloomf
date: 2017-10-11
tags: ml, literate-haskell
---

*Machine learning* is an awful name for a really simple idea.

For me, that name conjures up images of impossibly complex intelligent robots, and it gets worse with terms like "feedforward", "backpropagation", "neural network", and "perceptron". Combined with the seemingly magical applications of ML, for a long time I assumed it was one of those things I just didn't have the spare energy to understand.

I finally took the plunge and enrolled in Andrew Ng's Coursera course on machine learning, and it turns out I was wrong. Really wrong! The technical ideas -- the "how" -- of machine learning are accessible to anyone with exposure to calculus. Finding good data and using the right parameters -- the "what" and "why" -- are different questions, and more complicated. The apparent magic of ML comes from two observations: first, advances in computer hardware allow this simple idea to be applied to larger and larger problems, and second, the coolness of ML applications is superlinear as a function of problem size -- a problem twice as large might have a solution that is 4 times as cool. :)

Anyway, the simple idea behind (supervised) machine learning is roughly this, in my words:

1. Suppose we have an interesting but *unknown* function $F$, and some sample input-output pairs -- say some $(x,y)$ with $F(x) = y$.
2. Pretend that $F$ can be approximated by a *known* function $G_\theta$, which is parameterized by one or more variables $\theta$.
3. Use calculus to find the values of the $\theta$ that makes $G$ agree with our samples as closely as possible. That is, find $\theta$ so that $G_\theta(x) \approx y$.
4. Now use $G_\theta$ to make *predictions* about $F$, under the assumption that $G_\theta(x) \approx F(x)$ for all $x$.

The thing is, that function $F$ could do something really useful, like decide whether a photo includes a human face, or whether a credit card transaction is fraudulent.

It turns out this strategy for approximating $F$ works really well.

Ok -- so what $G_\theta$ look like? It needs to be complicated enough to be able to approximate $F$, but also simple enough that we can evaluate it and its gradient efficiently. (Incidentally, this kind of "sweet spot" between complexity and tractibility shows up a lot.) Typically $G_\theta$ is modeled using a *neural network*. And again -- that sounds complicated.

A google image search for "neural network" brings up a bunch of pictures like this:

![](/raw/gfx/dot/three-layer-neural-network.png){width=50%}

With "weights" and "nodes" in "layers" and "activation functions". Where's $F$ in this picture? Well, essentially, each column of nodes in that graph represents $\mathbb{R}^n$ for some $n$, and each node is a function of the nodes that point to it. Specifically, that function may be matrix multiplication, or a pointwise logistic, or something more complex.

For me, this way of visualizing neural networks is not helpful at all. For one thing it  includes a lot of junk; all those arrows don't convey very much information. What we have is a function from the leftmost layer to the middle layer, and another function from the middle layer to the rightmost layer. The first layer has 3 pieces of data, the middle has 4, and the last has 2. I'm more comfortable visualizing this as a chain like so. $$\mathbb{R}^3 \stackrel{\psi}{\rightarrow} \mathbb{R}^4 \stackrel{\phi}{\rightarrow} \mathbb{R}^2$$ Lo and behold, this is a diagram, representing ordinary function composition, where each arrow takes an extra parameter. Then $G$ is the composite of these arrows, and $\theta$ is the $\phi$ and $\psi$.

In this series of posts we'll develop a crude algebra of neural networks
