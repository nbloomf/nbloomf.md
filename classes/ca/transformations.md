---
title: Transformations
---

We can ask Google to plot some equations for us. Note that (as of this writing) google's plotter can only handle equations of the form $$y = \mathrm{some\ stuff\ not\ involving}\ y,$$ so we have to solve our equations for $y$ first. This is not always possible, and may require more than one equation!

## Shifts (a.k.a. Translation)

* [Horizontally Shifted Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%28x-3%29^2%29%2C+y+%3D+-sqrt%281+-+%28x-3%29^2%29): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad (x-3)^2 + y^2 = 1$$
* [Vertically Shifted Line](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+%282%2F3%29x+%2B+1%2F3%2C+y+%3D+%282%2F3%29x+%2B+1%2F3+-+2): $$2x - 3y + 1 = 0 \quad \mathrm{versus} \quad 2x - 3(y+2) + 1 = 0$$
* [Shifted Elliptic](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%28x^3+-+x%29%2C+y+%3D+-sqrt%28x^3+-+x%29%2C+y+%3D+sqrt%28%28x-3%29^3+-+%28x-3%29%29+%2B+2%2C+y+%3D+-sqrt%28%28x-3%29^3+-+%28x-3%29%29+%2B++2): $$y^2 = x^3 - x \quad \mathrm{versus} \quad (y-2)^2 = (x-3)^3 - (x-3)$$

## Stretches (a.k.a. Dilation)

* [Horizontally Stretched Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%28x%2F2%29^2%29%2C+y+%3D+-sqrt%281+-+%28x%2F2%29^2%29): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad \left(\frac{1}{2}x\right)^2 + y^2 = 1$$
* [Horizontally Shrunk (Shrinked? Shrank?) Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%282x%29^2%29%2C+y+%3D+-sqrt%281+-+%282x%29^2%29): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad (2x)^2 + y^2 = 1$$

## COMBO

Watch out for order of operations!

* [Horizontally Flipped and Vertically Shifted Elliptic](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%28x^3+-+x%29%2C+y+%3D+-sqrt%28x^3+-+x%29%2C+y+%3D+sqrt%28%28-x%29^3+-+%28-x%29%29+%2B+2%2C+y+%3D+-sqrt%28%28-x%29^3+-+%28-x%29%29+%2B+2): $$y^2 = x^3 - x \quad \mathrm{versus} \quad (y-2)^2 = (-x)^3 - (-x)$$
* [Shifted and Stretched Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%282%28x+-+3%29%29^2%29-4%2C+y+%3D+-sqrt%281+-+%282%28x-3%29%29^2%29-4): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad (2(x-3))^2 + (y+4)^2 = 1$$

## Extras: Rotation about the origin

* [Rotated Quadratic](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+x^2%2C+y+%3D+%28-cos%2810%29*%282*x*sin%281%2F2%29+%2B+1%29+%2B+sqrt%284*x*sin%281%2F2%29*sin%282*1%2F2%29+%2B+%28cos%281%2F2%29%29^2%29%29%2F%282*%28sin%281%2F2%29%29^2%29%2C+y+%3D+%28-cos%2810%29*%282*x*sin%281%2F2%29+%2B+1%29+-+sqrt%284*x*sin%281%2F2%29*sin%282*1%2F2%29+%2B+%28cos%281%2F2%29%29^2%29%29%2F%282*%28sin%281%2F2%29%29^2%29): $y = x^2$ versus $$x\sin(1/2) - y\cos(1/2) = (x\cos(1/2) + y\sin(1/2))^2$$ (clockwise rotation by 1/2 radian. Both of these should pass through the origin, but the second one doesn't. Why?)

## Bizarro Examples

The above transformations are achieved by replacing all the instances of $x$ and $y$ in an equation with some fixed **linear combinations** of $x$ and $y$. What happens if we replace the $x$ and $y$ with other stuff?

* [A Squared Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%28x^2%29^2%29%2B3%2C+y+%3D+-sqrt%281+-+%28x^2%29^2%29%2B3): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad (x^2)^2 + (y-3)^2 = 1$$
* [An Inverted Circle](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%281%2Fx%29^2%29%2B3%2C+y+%3D+-sqrt%281+-+%281%2Fx%29^2%29%2B3): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad \left(\frac{1}{x}\right)^2 + (y-3)^2 = 1$$
* [Kidney Bean?](https://www.google.com/?gws_rd=ssl#q=plot+y+%3D+sqrt%281+-+x^2%29%2C+y+%3D+-sqrt%281+-+x^2%29%2C+y+%3D+sqrt%281+-+%281%2Fx+%2B+abs%28x%29%29^2%29%2B3%2C+y+%3D+-sqrt%281+-+%281%2Fx+%2B+abs%28x%29%29^2%29%2B3): $$x^2 + y^2 = 1 \quad \mathrm{versus} \quad \left(\frac{1}{x} + |x|\right)^2 + (y-3)^2 = 1$$