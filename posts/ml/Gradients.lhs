---
title: Gradients
author: nbloomf
date: 2017-10-17
tags: ml, literate-haskell
---

Boilerplate.

> module Gradients where
> 
> import Control.Applicative
> import Test.QuickCheck
> import Test.QuickCheck.Test
> 
> import Indices
> import IndexIsos
> import Tensors
> import TensorFunctions

We'd like to do some calculus on tensor functions.

First some review on derivatives. If $f : \mathbb{R} \rightarrow \mathbb{R}$ is a function, then the <em>derivative</em> of $f$ at $x \in \mathbb{R}$, denoted $(Df)(x)$, is given by $$(Df)(x) = \lim_{h \rightarrow 0} \frac{f(x+h) - f(x)}{h},$$ if the limit exists. In this case we say $f$ is <em>differentiable</em> at $x \in \mathbb{R}$. We can think of $Df$ as a function $\mathbb{R} \rightarrow \mathbb{R}$. In a concrete sense, $(Df)(x)$ is the slope of the best linear approximation to $f$ at $x$.

This notion of "best linear approximation" is a useful one, so a natural question is how to generalize it to other kinds of functions. In particular, to functions that take more than one input and produce more than one output; say with signature $\mathbb{R}^m \rightarrow \mathbb{R}^n$. This is a little more complicated. First off, note that we don't really need to consider functions with more than one output, since any such function can be constructed out of one-output functions using the universal property of cartesian products. In concrete terms, a function $f : \mathbb{R}^2 \rightarrow \mathbb{R}^2$ like $$f(x,y) = (2x+y, x-3y)$$ is induced by the "coordinate functions" $f_1(x,y) = 2x+y$ and $f_2(x,y) = x-3y$. So we're really interested in finding a "derivative" for functions like $f : \mathbb{R}^m \rightarrow \mathbb{R}$.

We already know how to take derivatives of functions with one input, so one idea is to shoehorn $f$ into taking only one input, and differentiating that. Say $v \in \mathbb{R}^m$ is the point where we want the derivative, and choose some index $k \in m$. We now define a map $w_{k,v} : \mathbb{R} \rightarrow \mathbb{R}^m$ piecewise like so: $$w_{k,v}(x)_i = \left\{ \begin{array}{ll} v_i & \mathrm{if}\ i \neq k \\ x & \mathrm{if}\ i = k. \end{array} \right.$$ That is, $w_{k,v}(x)$ is $x$ in the $k$th coordinate, and agrees with $v$ everywhere else. Now $f \circ w_{k,v}$ is a map $\mathbb{R} \rightarrow \mathbb{R}$, so we can take its derivative in the usual way. This is called the $k$th <em>partial derivative</em> of $f$ at $v$, and sometimes denoted $(\frac{\partial}{\partial x_k}f)(v)$. That is, we define $$\left(\frac{\partial}{\partial x_k}f\right)(v) = D(f(w_{k,v}(x)))(v).$$

The full "derivative" of a multivariate function, called the <em>gradient</em>, is the tensor of partial derivatives at each coordinate. This tensor is also called the Jacobian.

More precisely: the gradient of a tensor function $f : \mathbb{R}^A \rightarrow \mathbb{R}^B$ at a point $v \in \mathbb{R}^A$, denoted $(\nabla f)(v)$, is a tensor in $\mathbb{R}^{B \otimes A}$, whose entry at $b \& a \in B \otimes A$ is given by $$(\nabla f)(v)_{b \& a} = D(f(w_{a,v}(x))_b)(v_a).$$ We can think of $\nabla f$ as a mapping with signature $$\mathbb{R}^A \rightarrow \mathbb{R}^{B \otimes A}.$$ Like the univariate derivative, the gradient also represents a "best linear approximation" at a point, although "line" now means "$n$-dimensional hyperplane" and everything is hard to visualize.

This definition for gradient is scary at first, but take heart: it means that finding the derivative of a hairy multivariate function requires nothing more than (1) computing plain old univariate derivatives and (2) maybe some intricate case analysis on tensor indices. Those things are tedious, but not super difficult. This is good news. :)


Example: "Linear" Functions
---------------------------

As an example, let's compute a concrete gradient. Let $H$ and $K$ be tensor sizes, and say we have tensors $M \in \mathbb{R}^{K \otimes H}$ and $B \in \mathbb{R}^K$. We can define a tensor function $f : \mathbb{R}^H \rightarrow \mathbb{R}^K$ by $$f(V) = MV + B,$$ where $MV$ denotes "matrix"-"vector" multiplication and $+$ is pointwise addition. Then $\nabla f$ is a function with signature $\mathbb{R}^H \rightarrow \mathbb{R}^{K \otimes H}$. Given some $V \in \mathbb{R}^H$ and $k \& h \in K \otimes H$, the $k \& h$ entry of the gradient of $f$ at $V$ is

$$\begin{eqnarray*}
 &   & (\nabla f)(V)_{k \& h} \\
 & = & D(f(w_{h,V}(x))_k)(V_h) \\
 & = & D((Mw_{h,V}(x) + B)_k)(V_h) \\
 & = & D((Mw_{h,V}(x))_k + B_k)(V_h) \\
 & = & D\left(\sum_{i \in H} M_{k \& i} w_{h,V}(x)_i + B_k\right)(V_h) \\
 & = & D\left(M_{k \& h}w_{h,V}(x)_h + \sum_{i \in H, i \neq h} M_{k \& i} w_{h,V}(x)_i + B_k\right)(V_h) \\
 & = & D\left(M_{k \& h}x + \sum_{i \in H, i \neq h} M_{k \& i}V_i + B_k\right)(V_h) \\
 & = & D(M_{k \& h}x)(V_h) \\
 & = & \overline{M_{k \& h}}(V_h) \\
 & = & M_{k \& h}
\end{eqnarray*}$$

In the fourth to last line we use the fact that the derivative is additive, and the derivative of a constant function is zero. In the second to last line, we use $\overline{\alpha}$ to denote the constant function returning $\alpha$.

That is:

<div class="result">
<div class="thm">
Fix $M \in \mathbb{R}^{K \otimes H}$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^H \rightarrow \mathbb{R}^K$ by $f(X) = MX + B$. Then $$\nabla f : \mathbb{R}^{H} \rightarrow \mathbb{R}^{K \otimes H}$$ is given by $$(\nabla f)(X) = M.$$
</div>
</div>

So $\nabla f$ is a constant function, always returning $M$.

We can also think of $MX+B$ as a function of $M$. That is, fix $V \in \mathbb{R}^H$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^K$ by $$f(M) = MV + B.$$ Now $$\nabla f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^{K \otimes (K \otimes H)}.$$ If $t\&(k\&h) \in K \otimes (K \otimes H)$, we have two possibilities, depending on whether $t = k$ or not. If $t \neq k$, we have

$$\begin{eqnarray*}
 &   & (\nabla f)(M)_{t\&(k\&h)} \\
 & = & D(f(w_{k\&h,M}(x))_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V + B)_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V)_t + B_t)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} M_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & \overline{0}(M_{k\&h}) \\
 & = & 0,
\end{eqnarray*}$$

and if $t = k$ we have

$$\begin{eqnarray*}
 &   & (\nabla f)(M)_{t\&(k\&h)} \\
 & = & D(f(w_{k\&h,M}(x))_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V + B)_t)(M_{k\&h}) \\
 & = & D((w_{k\&h,M}(x)V)_t + B_t)(M_{k\&h}) \\
 & = & D\left(\sum_{i \in H} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(w_{k\&h,M}(x)_{t\&h}V_h + \sum_{i \in H, i \neq h} w_{k\&h,M}(x)_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D\left(xV_h + \sum_{i \in H, i \neq h} M_{t\&i}V_i + B_t\right)(M_{k\&h}) \\
 & = & D(xV_h)(M_{k\&h}) \\
 & = & \overline{V_h}(M_{k\&h}) \\
 & = & V_h.
\end{eqnarray*}$$

That is:

<div class="result">
<div class="thm">
Fix $V \in \mathbb{R}^H$ and $B \in \mathbb{R}^K$, and define $f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^K$ by $f(M) = MV + B$. Then $$\nabla f : \mathbb{R}^{K \otimes H} \rightarrow \mathbb{R}^{K \otimes (K \otimes H)}$$ is given by  $$(\nabla f)(M)_{t\&(k\&h)} = \left\{\begin{array}{ll} V_h & \mathrm{if}\ t = k \\ 0 & \mathrm{otherwise}. \end{array}\right.$$
</div>
</div>

We can take this one step further. An expression like $MV + B$ can be thought of as a function of $M$, $V$, and $B$ simultaneously; define $$f : \mathbb{R}^{((K \otimes H) \oplus K) \oplus H} \rightarrow \mathbb{R}^k$$ by $$f((M \oplus B) \oplus V) = MV + B.$$ Then $$\nabla(f) : \mathbb{R}^{((K \otimes H) \oplus K) \oplus H} \rightarrow \mathbb{R}^{K \otimes (((K \otimes H) \oplus K) \oplus H)}.$$ We can compute this gradient one component at a time by breaking it into cases. Note that the components of $\nabla(f)(X)$ come in three flavors: $k \& \mathsf{L}\mathsf{L}(i \& j)$ where $k,i \in K$ and $j \in H$, $k \& \mathsf{L}\mathsf{R}(s)$ where $k,s \in K$, and $k \& \mathsf{R}(t)$ where $k \in K$ and $t \in H$. We consider each case in turn.

First, at $k \& \mathsf{L}\mathsf{L}(i \& j)$ when $i \neq k$:

$$\begin{eqnarray*}
 &   & (\nabla f)((M \oplus B) \oplus V)_{k \& \mathsf{L}\mathsf{L}(i \& j)} \\
 & = & D(f(w_{\mathsf{L}\mathsf{L}(i \& j), (M \oplus B) \oplus V}(x))_k)(((M \oplus B) \oplus V)_{\mathsf{L}\mathsf{L}(i \& j)}) \\
 & = & D(f((w_{i \& j, M}(x) \oplus B) \oplus V)_k)(M_{i \& j}) \\
 & = & D((w_{i \& j, M}(x)V + B)_k)(M_{i \& j}) \\
 & = & D((w_{i \& j, M}(x)V)_k + B_k)(M_{i \& j}) \\
 & = & D\left(\sum_{h \in H} w_{i \& j, M}(x)_{k \& h} V_h\right)(M_{i,j}) \\
 & = & D\left(\sum_{h \in H} M_{k \& h} V_h\right)(M_{i,j}) \\
 & = & 0
\end{eqnarray*}$$

Next, at $k \& \mathsf{L}\mathsf{L}(i \& j)$ when $i = k$:

$$\begin{eqnarray*}
 &   & (\nabla f)((M \oplus B) \oplus V)_{k \& \mathsf{L}\mathsf{L}(i \& j)} \\
 & = & D(f(w_{\mathsf{L}\mathsf{L}(i \& j), (M \oplus B) \oplus V}(x))_k)(((M \oplus B) \oplus V)_{\mathsf{L}\mathsf{L}(i \& j)}) \\
 & = & D(f((w_{i \& j, M}(x) \oplus B) \oplus V)_k)(M_{i \& j}) \\
 & = & D((w_{i \& j, M}(x)V + B)_k)(M_{i \& j}) \\
 & = & D((w_{i \& j, M}(x)V)_k + B_k)(M_{i \& j}) \\
 & = & D\left(\sum_{h \in H} w_{i \& j, M}(x)_{k \& h} V_h\right)(M_{i,j}) \\
 & = & D\left(xV_j + \sum_{h \in H, h \neq j} w_{i \& j, M}(x)_{k \& h} V_h\right)(M_{i,j}) \\
 & = & D(xV_j)(M_{i,j}) \\
 & = & \overline{V_j}(M_{i,j}) \\
 & = & V_j
\end{eqnarray*}$$

Now at $k \& \mathsf{L}\mathsf{R}(s)$ if $s \neq k$:

$$\begin{eqnarray*}
 &   & (\nabla f)((M \oplus B) \oplus V)_{k \& \mathsf{L}\mathsf{R}(s)} \\
 & = & D(f(w_{\mathsf{L}\mathsf{R}(s), (M \oplus B) \oplus V}(x))_k)(((M \oplus B) \oplus V)_{\mathsf{L}\mathsf{R}(s)}) \\
 & = & D(f((M \oplus w_{s, B}(x)) \oplus V)_k)(B_s) \\
 & = & D((MV + w_{s,B}(x))_k)(B_s) \\
 & = & D((MV)_k + w_{s,B}(x)_k)(B_s) \\
 & = & D(w_{s,B}(x)_k)(B_s) \\
 & = & D(B_k)(B_s) \\
 & = & 0
\end{eqnarray*}$$

and at $k \& \mathsf{L}\mathsf{R}(s)$ if $s = k$:

$$\begin{eqnarray*}
 &   & (\nabla f)((M \oplus B) \oplus V)_{k \& \mathsf{L}\mathsf{R}(s)} \\
 & = & D(f(w_{\mathsf{L}\mathsf{R}(s), (M \oplus B) \oplus V}(x))_k)(((M \oplus B) \oplus V)_{\mathsf{L}\mathsf{R}(s)}) \\
 & = & D(f((M \oplus w_{s, B}(x)) \oplus V)_k)(B_s) \\
 & = & D((MV + w_{s,B}(x))_k)(B_s) \\
 & = & D((MV)_k + w_{s,B}(x)_k)(B_s) \\
 & = & D(w_{s,B}(x)_k)(B_s) \\
 & = & D(x)(B_s) \\
 & = & \overline{1}(B_s) \\
 & = & 1
\end{eqnarray*}$$

Finally, at $k \& \mathsf{R}(t)$:

$$\begin{eqnarray*}
 &   & (\nabla f)((M \oplus B) \oplus V)_{k \& \mathsf{R}(t)} \\
 & = & D(f(w_{\mathsf{R}(t), (M \oplus B) \oplus V}(x))_k)(((M \oplus B) \oplus V)_{\mathsf{R}(t)}) \\
 & = & D(f((M \oplus B) \oplus w_{t,V}(x))_k)(V_t) \\
 & = & D((Mw_{t,V}(x) + B)_k)(V_t) \\
 & = & D((Mw_{t,V}(x))_k + B_k)(V_t) \\
 & = & D((Mw_{t,v}(x))_k)(V_t) \\
 & = & D\left( \sum_{h \in H} M_{k \& h} w_{t,V}(x)_h \right)(V_t) \\
 & = & D\left( M_{k,t}x + \sum_{h \in H, h \neq t} M_{k \& h} V_h \right)(V_t) \\
 & = & D(M_{k,t}x)(V_t) \\
 & = & \overline{M_{k,t}}(V_t) \\
 & = & M_{k,t}.
\end{eqnarray*}$$

That's a mouthful. :) Anyway, we'll use this hideous gradient later.

Another useful gradient is that for a direct sum function. Let $u$ and $v$ be sizes, and let $B \in \mathbb{R}^v$ be fixed. We can define a map $f : \mathbb{R}^u \rightarrow \mathbb{R}^{u \oplus v}$ by $$f(A) = A \oplus B.$$ Now the gradient of $f$ has signature $$\nabla f : \mathbb{R}^u \rightarrow \mathbb{R}^{(u \oplus v) \otimes u},$$ and we can calculate its value at a given index. Note that the indices of $(\nabla f)(V)$ come in two flavors: $\mathsf{L}(i) \& k$ where $i, k \in u$, and $\mathsf{R}(j) \& k$ where $k \in u$ and $j \in v$.

At $\mathsf{L}(i) \& k$ with $i \neq k$, we have

$$\begin{eqnarray*}
 &   & \nabla(f)(V)_{\mathsf{L}(i) \& k} \\
 & = & D(f(w_{k,V}(x))_{\mathsf{L}(i)})(V_k) \\
 & = & D((w_{k,V}(x) \oplus B)_{\mathsf{L}(i)})(V_k) \\
 & = & D(w_{k,V}(x)_i)(V_k) \\
 & = & D(V_i)(V_k) \\
 & = & \overline{0}(V_k) \\
 & = & 0
\end{eqnarray*}$$

while at $\mathsf{L}(i) \& k$ with $i = k$, we have

$$\begin{eqnarray*}
 &   & \nabla(f)(V)_{\mathsf{L}(i) \& k} \\
 & = & D(f(w_{k,V}(x))_{\mathsf{L}(i)})(V_k) \\
 & = & D((w_{k,V}(x) \oplus B)_{\mathsf{L}(i)})(V_k) \\
 & = & D(w_{k,V}(x)_i)(V_k) \\
 & = & D(x)(V_k) \\
 & = & \overline{1}(V_k) \\
 & = & 1.
\end{eqnarray*}$$

And at $\mathsf{R}(j) \& k$, we have

$$\begin{eqnarray*}
 &   & \nabla(f)(V)_{\mathsf{R}(j) \& k} \\
 & = & D(f(w_{k,V}(x))_{\mathsf{R}(j)})(V_k) \\
 & = & D((w_{k,V}(x) \oplus B)_{\mathsf{R}(j)})(V_k) \\
 & = & D(B_j)(V_k) \\
 & = & \overline{0}(V_k) \\
 & = & 0.
\end{eqnarray*}$$

Putting this together, we have $$\nabla(- \oplus B)(V) = \mathsf{vcat}(\mathsf{Id}(u), \mathsf{Z}(v \otimes u)).$$ Similarly, $$\nabla(A \oplus -)(V) = \mathsf{vcat}(\mathsf{Z}(v \otimes u), \mathsf{Id}(u)).$$

Linearity and the Chain Rule
----------------------------

The gradient defined above is computationally useful, but not theoretically enlightening. It turns out that the usual definition of derivative for univariate functions generalizes nicely to general multivariate functions. The search term here is [Fréchet derivative](https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative). There is an alternative characterization of derivatives, due to Carathéodory, that makes the proofs of linearity and the chain rule for derivatives really clear, and this characterization also generalizes really nicely. I'm not super interested in retyping those proofs here, so I'll just link to the paper [Fréchet vs. Carathéodory](http://www.docentes.unal.edu.co/eacostag/docs/FreCarat_Acosta.pdf), by Acosta and Delgado, where I saw them.

The point is that as a function, gradient is linear in the sense that $$\nabla(\alpha f + \beta g) = \alpha (\nabla f) + \beta (\nabla g)$$ for tensor functions $f$ and $g$ and real numbers $\alpha$ and $\beta$ so long as the signatures make sense.

Moreover we have a multivariate chain rule. If $f$ and $g$ are tensor functions and $g \circ f$ makes sense, then $$\nabla(g \circ f)(V) = \nabla(g)(f(V)) \cdot \nabla(f)(V),$$ where the $\cdot$ denotes tensor contraction (a.k.a. matrix multiplication). The proof of this is complicated and technical if we use Fréchet's definition of the derivative and is <em>almost</em> trivial if we use Carathéodory's definition. I'll refer to the paper for details, but we can at least check that the types make sense. Say $f : \mathbb{R}^A \rightarrow \mathbb{R}^B$ and $g : \mathbb{R}^B \rightarrow \mathbb{R}^C$. Then $\nabla g : \mathbb{B} \rightarrow \mathbb{R}^{C \otimes B}$ and $\nabla f : \mathbb{R}^A \rightarrow \mathbb{R}^{B \otimes A}$. If $V \in \mathbb{R}^A$, then $f(V) \in \mathbb{R}^B$, and $(\nabla g)(f(V)) \in \mathbb{R}^{C \otimes B}$. We also have $\nabla(f)(V) \in \mathbb{R}^{B \otimes A}$, and the final contraction gives $$\nabla(g)(f(V)) \cdot \nabla(f)(V) \in \mathbb{R}^{C \otimes A}$$ as expected.

The chain rule is especially nice. It means that to evaluate the gradient of $g \circ f$ at a tensor $V$, all we need to know is (1) the value of $f$ at $V$, (2) the gradient of $g$ at $f(V)$, and (3) the gradient of $f$ at $V$. We will use this later in a big way.
