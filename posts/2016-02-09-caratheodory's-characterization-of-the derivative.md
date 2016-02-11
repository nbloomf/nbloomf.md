---
title: Carathéodory's characterization of the derivative
author: nbloomf
date: 2016-02-09
---

Today I came upon a very nice idea in calculus, completely by accident, while preparing some lecture notes. Maybe this is well-known, but calculus and analysis have always been weak spots for me and I found the idea to be very enlightening.

Calculus is a nice place to start introducing students to the idea of mathematical proof; they tend to have enough confidence in their algebra skills that "why" questions are becoming more important. And so, I try to include some proofs here and there. One result, however, whose usual textbook proof has always seemed unsatisfying to me is the Chain Rule.

<div class="result">
Let $f$ and $g$ be real functions such that $g$ is differentiable at $a$ and $f$ is differentiable at $g(a)$. Then $f \circ g$ is differentiable at $a$, and moreover $$(f \circ g)^\prime (a) = f^\prime(g(a)) \cdot g^\prime(a).$$
</div>

The proof given in most textbooks I've used involves introducing new variables in a way that strikes me as a little too handwavy.

I poked around online looking for alternative proofs and found a paper by Stephen Kuhn in the American Math Monthly called "The Derivative á la Carathéodory". The main idea, attributed to a textbook written by Constantin Carathéodory, is the following alternative characterization of differentiability.

<div class="result">
Let $f$ be a real function and $a$ a real number. Then $f$ is differentiable at $a$ if and only if there exists a real function $\varphi$ such that $\varphi$ is continuous at $a$ and for all $x$, $$f(x) - f(a) = \varphi(x)(x-a).$$ In this case, we have $\varphi(a) = f^\prime(a)$.
</div>

Where differentiability is defined as usual via the limit of a difference quotient.

<div class="result">
Let $f$ be a real function and $a$ a real number. We say that $f$ is differentiable at $a$ if $$\lim_{x \rightarrow a} \frac{f(x)-f(a)}{x-a}$$ exists. In this case, the value of this limit is denoted $f^\prime(a)$ and called the derivative of $f$ at $a$. The real function $x \mapsto f^\prime(x)$ is called the derivative of $f$.
</div>

It is straightforward to show that Carathéodory's characterization is equivalent to the limit-based definition. And while it is less concrete for computational purposes, Carathéodory makes the proof of the chain rule very slick (and not at all handwavy, to my taste).

<div class="result">
<div class="proof">
(Chain Rule.) Let $f$ and $g$ be real functions and $a$ a real number such that $g$ is differentiable at $a$ and $f$ differentiable at $g(a)$. By Carathéodory's characterization, there is a function $\varphi$ such that $$g(x) - g(a) = \varphi(x)(x-a)$$ for all $x$ and a function $\psi$ such that $$f(y) - f(g(a)) = \psi(y)(y - g(a))$$ for all $y$; in particular for $y = g(x)$. Now substituting yields $$f(g(x)) - f(g(a)) = \psi(g(x))\varphi(x)(x-a).$$ Since $g$ is differentiable at $a$, it is continuous at $a$, and so $\psi(g(x))$ is continuous at $a$, and thus $\psi(g(x))\varphi(x)$ is continuous at $a$. Again by Carathéodory, $f \circ g$ is differentiable at $a$, and $$(f \circ g)^\prime(a) = \psi(g(a))\varphi(a) = f^\prime(g(a)) \cdot g^\prime(a).$$
</div>
</div>

Nice. :)

On the one hand, I can see why this idea has gotten left out of more modern books. Often calculus is a cookbook class where the emphasis is on computation rather than abstract understanding. (And that "there exists" in Carathéodory's characterization might be scary.) On the other hand, the idea is so beautiful, and following the paper "Fréchet vs. Carathéodory" by Ernesto Acosta G. and Cesar Delgado G., also in American Math Monthly, generalizes nicely.

I think I'll use this next time I teach calculus.
