---
title: The Primitive Recursion Theorem
---

In the last section, we defined the natural numbers as an iterative set with a special *universal property*, which was encapsulated in the existence of a simple recursion operator \\(\\natrec{\\ast}{\\ast}\\). Anything we will wish to do with the natural numbers can be done using this operator alone. However, in practice, it will be handy to define synonyms for some more complicated recursive functions.

<div class="result">
<div class="thm">
Suppose we have sets \\(A\\) and \\(B\\) and functions \\(\\varphi : A \\rightarrow B\\) and \\(\\mu : \\nats \\times A \\times B \\rightarrow B\\). Then there is a unique function \\(\\Theta : \\nats \\times A \\rightarrow B\\) such that, for all \\(n \\in \\nats\\) and \\(a \\in A\\), \\[\\begin{eqnarray\*} \\Theta(\\zero, a) & = & \\varphi(a)\\ \\mathrm{and} \\\\ \\Theta(\\next(n), a) & = & \\mu(n, a, \\Theta(n, a)). \\end{eqnarray\*} \\]

This function \\(\\Theta\\) will be denoted \\(\\primrec{\\varphi}{\\mu}\\).
</div>

<div class="proof">
First, define a mapping \\(t : \\nats \\times {}^AB \\rightarrow \\nats \\times {}^AB\\) by \\[t(n,h) = (\\next(n), \\lambda x : \\mu(n, x, h(x))).\\] Note that we are using the \\(\\lambda\\) notation to define an anonymous function \\(A \\rightarrow B\\) on the right hand side; specifically, \\(\\lambda x : \\mu(n, x, h(x))\\) is the function \\(q : A \\rightarrow B\\) such that \\(q(x) = \\mu(n,x,h(x))\\).

Now we define \\(\\Theta\\) as follows: \\[\\Theta(n,a) = (\\pi_2 \\circ \\natrec{(0, \\varphi)}{t})(n)(a).\\]
</div>
</div>

> module PrimitiveRecursion where
>
> primRecur :: (a -> b) -> (Nat -> a -> b) -> Nat -> a -> b
> primRecur phi _  Zero     a = phi a
> primRecur phi mu (Next n) a = mu n a (primRecur phi mu n a)
