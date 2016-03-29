---
title: Addition
author: nbloomf
---

So far we've characterized the natural numbers via a unique mapping $\natrec{\ast}{\ast} : \nats \rightarrow A$, and we defined another parameterized mapping $\primrec{\ast}{\ast} : \nats \times A \rightarrow B$. From now on, when we want to define a mapping with one of these signatures, these recursive maps may come in handy.

For example natural number addition has signature $\nats \times \nats \rightarrow \nats$, so we might hope to define addition in terms of $\primrec{\ast}{\ast}$ -- and in fact we can.

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
