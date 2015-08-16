---
title: Arithmetic
---

In the previous post, we defined the natural numbers in terms of a unique recursion operator \\(\\natrec{\\ast}{\\ast}\\). Now we will use this operator to define the usual arithmetic operations and prove that they behave as expected.

**Addition**

We'd like to define a function \\(\\nplus : \\nats \\times \\nats \\rightarrow \\nats\\) that behaves a certain way. But at the moment we only know of one way to define a function on \\(\\nats\\), using \\(\\natrec{\\ast}{\\ast}\\). How can we use this to define a function on \\(\\nats \\times \\nats\\)? We will use a neat trick called *currying*. Essentially, rather than constructing a function which takes two arguments \\(a\\) and \\(b\\) and returns \\(a+b\\), we construct a function which takes a single argument \\(a\\) and returns another function of a single argument \\(b\\) which returns \\(a+b\\). We need to come up with suitable \\(e\\) and \\(\\varphi\\) so that \\[\\natrec{e}{\\varphi} : \\nats \\rightarrow (\\nats \\rightarrow \\nats)\\] behaves like \\(\\nplus\\). But how does \\(\\nplus\\) behave? We certainly should have \\(0 + a = a\\) for all \\(a\\). That is, \\[a = \\natrec{e}{\\varphi}(\\zero)(a) = e(a)\\] for all \\(a\\); thus \\(e = \\id\\). Similarly we must have \\((1+n)+a = 1+(n+a)\\) for all \\(n\\) and \\(a\\), so that \\[\\next(\\natrec{e}{\\varphi}(n)(a)) = \\natrec{e}{\\varphi}(\\next(n))(a) = \\varphi(\\natrec{e}{\\varphi}(n))(a).\\] Thus \\(\\varphi(f)(m) = \\next(f(m))\\).

<div class="result">
<div class="defn">
<p>Let \\(\\varphi : (\\nats \\rightarrow \\nats) \\rightarrow (\\nats \\rightarrow \\nats)\\) be the mapping given by \\(\\varphi(f)(m) = \\next(f(m))\\). We define a special function \\(\\nplus : \\nats \\times \\nats \\rightarrow \\nats\\) by \\[\\nplus(a,b) = \\natrec{\\id}{\\varphi}(a)(b).\\]</p>
</div>
</div>

<div class="result">
<div class="lemma">
The following hold for all natural numbers \\(a\\), \\(b\\), and \\(c\\).

1. \\(\\nplus(0, a) = a\\)
2. \\(\\nplus(\\next(a), b) = \\next(\\nplus(a, b)) = \\nplus(a, \\next(b))\\)
3. \\(\\nplus(a, 0) = a\\).
4. \\(\\nplus(a, b) = \\nplus(b, a)\\).
5. \\(\\nplus(a, \\nplus(b, c)) = \\nplus(\\nplus(a, b), c)\\).
6. If \\(\\nplus(a, c) = \\nplus(b, c)\\) then \\(a = b\\).
</div>

<div class="proof">

1. Note first that \\[\\nplus(0, a) = \\natrec{\\id}{\\varphi}(\\zero)(a) = \\id(a) = a.\\]
2. To see the first equality, note that \\[\\begin{eqnarray\*} \\nplus(\\next(a), b) & = & \\natrec{\\id}{\\varphi}(\\next(a))(b) \\\\ & = & \\varphi(\\natrec{\\id}{\\varphi}(a))(b) \\\\ & = & \\next(\\natrec{\\id}{\\varphi}(a)(b)) \\\\ & = & \\next(\\nplus(a, b)). \\end{eqnarray\*}\\] We show the second by induction. Define \\[B = \\{n \\in \\nats \\mid \\next(\\nplus(n, m)) = \\nplus(n, \\next(m))\\ \\mathrm{for\\ all}\\ m \\in \\nats\\}.\\] We have \\(\\zero \\in B\\) since for all \\(m\\), \\[\\next(\\nplus(\\zero, m)) = \\next(m) = \\nplus(\\zero, \\next(m)).\\] Now suppose \\(n \\in B\\), and let \\(m \\in \\nats\\). Then \\[\\begin{eqnarray\*} \\next(\\nplus(\\next(n), m)) & = & \\next(\\next(\\nplus(n, m))) \\\\ & = & \\next(\\nplus(n, \\next(m))) \\\\ & = & \\nplus(\\next(n), \\next(m)). \\end{eqnarray\*}\\] The conclusion follows.
3. We use induction. Define a set \\[B = \\{n \\in \\nats \\mid \\nplus(n, 0) = n \\}. \\] Certainly \\(\\zero \\in B\\). Now suppose \\(n \\in B\\); note that \\[\\nplus(\\next(n), \\zero) = \\next(\\nplus(n,0)) = \\next(n),\\] and thus \\(\\next(n) \\in B\\). The conclusion follows.
4. We again use induction. Define \\[B = \\{n \\in \\nats \\mid \\nplus(n, m) = \\nplus(m, n)\\ \\mathrm{for\\ all}\\ m \\in \\nats\\}.\\] We have \\(\\zero \\in B\\) since \\[\\nplus(\\zero, m) = m = \\nplus(m, \\zero)\\] for all \\(m\\). Now suppose \\(n \\in B\\), and let \\(m \\in \\nats\\). Then \\[\\begin{eqnarray\*} \\nplus(\\next(n), m) & = & \\next(\\nplus(n,m)) \\\\ & = & \\next(\\nplus(m,n)) \\\\ & = & \\nplus(m, \\next(n)) \\end{eqnarray\*} \\] as needed.
5. asf
6. asd

</div>
</div>



**Multiplication**

<div class="result">
<div class="defn">
We define three special functions \\(\\mathbb{N} \\rightarrow (\\mathbb{N} \\rightarrow \\mathbb{N})\\) as follows.

2. \\(\\ntimes = \\natrec{\\const(0)}{\\varphi}\\), where \\(\\varphi(f)(m) = \\nplus\\ m\\ f(m)\\).
</div>
</div>

1. \\(\\ntimes(a, \\zero) = \\ntimes(\\zero, a) = \\zero\\).
2. \\(\\ntimes(a, \\next(0)) = a\\) and \\(\\ntimes(\\next(0), a) = a\\).
3. $(a + b) \cdot c = (a \cdot c) + (b \cdot c)$.
4. $a \cdot b = b \cdot a$
5. $latex a \cdot (b + c) = (a \cdot b) + (a \cdot c)$
6. $latex a \cdot (b \cdot c) = (a \cdot b) \cdot c$.
7. If $latex a \cdot c = b \cdot c$ and $latex c \neq 0$, then $latex a = b$.  

1. $latex a \uparrow 0 = \mathsf{next}(0)$
2. $latex a \uparrow \mathsf{next}(0) = a$
3. $latex 0 \uparrow a = 0$ for all $latex a \neq 0$.
4. $latex \mathsf{next}(0) \uparrow a = \mathsf{next}(0)$
5. $latex a \uparrow (b+c) = (a \uparrow b) \cdot (a \uparrow c)$
6. $latex a \uparrow (b \cdot c) = (a \uparrow b) \uparrow c$
7. $latex (a \cdot b) \uparrow c = (a \uparrow c) \cdot (b \uparrow c)$

> module Arithmetic where
>
> import Natural

> plus :: Nat -> Nat -> Nat
> plus = natRecur id phi
>   where phi f m = Next (f m)

> times :: Nat -> Nat -> Nat
> times = natRecur (const Zero) phi
>   where phi f m = plus m (f m)

> power :: Nat -> Nat -> Nat
> power = natRecur (const (Next Zero)) phi
>   where phi f m = times m (f m)