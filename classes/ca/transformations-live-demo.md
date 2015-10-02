---
title: Transformations: A Live Demo
---

Given an equation in $x$ and $y$, if we replace all the instances of $x$ with $\frac{1}{a}(x-h)$, this has the effect of shifting the equation's graph horizontally by $|h|$ units (right if $h$ is positive, left if negative) and stretching the graph horizontally by a factor of $|a|$ with a flip across the $y$-axis if $a$ is negative. Likewise, replacing all instances of $y$ by $\frac{1}{b}(y-k)$ gives a vertical shift and stretch.

The widget below is a live demonstration of these transformations. The graph of an equation is plotted on a pair of Cartesian axes, and the sliders below can be used to tweak the values of $a$, $b$, $h$, and $k$. The graph updates on the fly. You can select several different base equations using the drop-down menu. The Reset button sets $a$ and $b$ to 1 and $h$ and $k$ to 0.

Note that there is no cheating going on: the graph is drawn by checking, for each pixel, whether the equation has a solution nearby, and coloring that pixel black if so.

<div style="text-align:center;">
<iframe src="../../raw/transformations-live-demo.html" width="560" height="480" style="border:none;"></iframe>
</div>

## Normal Equations

* Line: $$x-y=0 \quad \rightarrow \quad \frac{1}{a}(x-h) - \frac{1}{b}(y-k)=0$$
* Circle: $$x^2 + y^2 = 1 \quad \rightarrow \quad \left(\frac{1}{a}(x-h)\right)^2 + \left(\frac{1}{b}(y-k)\right)^2 = 1$$
* Quadratic: $$y = x^2 \quad \rightarrow \quad \left(\frac{1}{b}(y-k)\right) = \left(\frac{1}{a}(x-h)\right)^2$$
* Cubic: $$y = x^3 \quad \rightarrow \quad \frac{1}{b}(y-k) = \left(\frac{1}{a}(x-h)\right)^3$$

## Neat looking Equations

* Elliptic 1: $y^2 = x^3 - 2x$
* Elliptic 2: $y^2 = x^3 - 2x + 2$
* Ampersand: $(y^2 - x^2)(x-1)(2x-3) = 4(x^2 + y^2 - 2x)^2$
* Lemniscate: $(x^2 + y^2)^2 = 2(x^2 - y^2)$
* Devil's Curve: $y^2\left(y^2 - \frac{16}{25}\right) = x^2(x^2 - 1)$

## What about $t$?

If we replace all the $x$s with $x\cos(t) - y\sin(t)$ and all the $y$s with $x\sin(t) + y\cos(t)$, this rotates the graph about the origin by $t$ radians (clockwise if $t$ is positive and counterclockwise if negative). Here the rotation happens after the shifting and stretching, which is why fiddling with the $h$ and $k$ parameters when $t$ is not zero don't correspond to horizontal and vertical shifts. This demo also converts the $t$ parameter from degrees.
