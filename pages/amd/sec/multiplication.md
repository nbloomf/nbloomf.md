---
title: Multiplication
author: nbloomf
---

(@@@)

<div class="result">
<div class="defn"><p>
Let $\mu : \nats \times \nats \times \nats \rightarrow \nats$ be given by $\mu(k,a,b) = \nplus(a,b)$. We then define $\ntimes : \nats \times \nats \rightarrow \nats$ by $$\ntimes = \primrec{\const(\zero)}{\mu}.$$
</p></div>
</div>

Showing that $\ntimes$ has the familiar properties of addition then comes down to a few applications of induction.

<div class="result">
<div class="thm">
The following hold for all natural numbers $a$, $b$, and $c$.

1. $\ntimes(\zero,a) = \zero = \ntimes(a,\zero)$.
2. $\ntimes(\next(\zero),a) = a = \ntimes(a,\next(\zero))$.
3. $\nplus(a,\ntimes(a,b)) = \ntimes(a,\next(b))$.
4. $\ntimes(a,b) = \ntimes(b,a)$.
5. $\ntimes(a,\nplus(b,c)) = \nplus(\ntimes(a,b),\ntimes(a,c))$.
6. $\ntimes(\nplus(b,c),a) = \nplus(\ntimes(b,a),\ntimes(c,a))$.
7. $\ntimes(\ntimes(a,b),c) = \ntimes(a,\ntimes(b,c))$.
</div>

<div class="proof"><p>
1. Note that $$\ntimes(\zero,a) = \primrec{\const(\zero)}{\mu}(\zero,a) = \const(\zero)(a) = \zero.$$ To show the second equality, we proceed by induction on $a$. For the base case note that $$\ntimes(\zero,\zero) = \zero.$$ Suppose now that the equation holds for some $a$. Then we have $$\begin{eqnarray*} \ntimes(\next(a),\zero) & = & \primrec{\const(\zero)}{\mu}(\next(a),\zero) \\ & = & \mu(a,\zero,\primrec{\const(\zero)}{\mu}(a,\zero)) \\ & = & \mu(a,\zero,\ntimes(a,\zero)) \\ & = & \mu(a,\zero,\zero) \\ & = & \nplus(\zero,\zero) \\ & = & \zero \end{eqnarray*}$$ as needed.
2. First note that $$\begin{eqnarray*} \ntimes(\next(\zero),a) & = & \primrec{\const(\zero)}{\mu}(\next(\zero),a) \\ & = & \mu(\zero,a,\primrec{\const(\zero)}{\mu}(\zero,a)) \\ & = & \mu(\zero,a,\ntimes(\zero,a)) \\ & = & \mu(\zero,a,\zero) \\ & = & \nplus(a,\zero) \\ & = & a. \end{eqnarray*}$$ To see the second equality, we proceed by induction on $a$. For the base case, note that $\ntimes(\zero,\next(\zero)) = \zero$. For the inductive step, suppose the equality holds for some $a$. Then we have $$\begin{eqnarray*} \ntimes(\next(a),\next(\zero)) & = & \primrec{\const(\zero)}{\mu}(\next(a), \next(\zero)) \\ & = & \mu(a,\next(\zero),\primrec{\const(\zero)}{\mu}(a,\next(\zero))) \\ & = & \mu(a,\next(\zero),\ntimes(a,\next(\zero))) \\ & = & \mu(a,\next(\zero),a) \\ & = & \nplus(\next(\zero),a) \\ & = & \next(\nplus(\zero,a)) \\ & = & \next(a) \end{eqnarray*}$$ as needed.
3. We proceed by induction on $a$. For the base case, note that $$\nplus(\zero,\ntimes(\zero,b)) = \nplus(\zero,\zero) = \zero = \ntimes(\zero,\next(b)).$$ For the inductive step, suppose the result holds for some $a$. Then we have $$\begin{eqnarray*} \nplus(\next(a),\ntimes(\next(a),b)) & = & \nplus(\next(a), \primrec{\const(\zero)}{\mu}(\next(a),b))) \\ & = & \nplus(\next(a), \mu(a,b,\primrec{\const(\zero)}{\mu}(a,b))) \\ & = & \nplus(\next(a), \mu(a,b,\ntimes(a,b))) \\ & = & \nplus(\next(a),\nplus(b,\ntimes(a,b)))\\ & = & \next(\nplus(a, \nplus(b, \ntimes(a,b)))) \\ & = & \next(\nplus(\nplus(a,b),\ntimes(a,b))) \\ & = & \next(\nplus(\nplus(b,a),\ntimes(a,b))) \\ & = & \next(\nplus(b, \nplus(a, \ntimes(a,b)))) \\ & = & \next(\nplus(b,\ntimes(a,\next(b)))) \\ & = & \nplus(\next(b),\ntimes(a,\next(b))) \\ & = & \mu(a,\next(b),\ntimes(a,\next(b))) \\ & = & \mu(a,\next(b),\primrec{\const(\zero)}{\mu}(a,\next(b))) \\ & = & \primrec{\const(\zero)}{\mu}(\next(a),\next(b)) \\ & = & \ntimes(\next(a),\next(b)) \end{eqnarray*}$$ as needed.
4. We proceed by induction on $a$. For the base case, note that $$\ntimes(\zero,b) = \zero = \ntimes(b,\zero).$$ For the inductive step, suppose the result holds for some $a$. Now $$\begin{eqnarray*} \ntimes(\next(a),b) & = & \primrec{\const(\zero)}{\mu}(\next(a),b) \\ & = & \mu(a,b,\primrec{\const(\zero)}{\mu}(a,b)) \\ & = & \mu(a,b,\ntimes(a,b)) \\ & = & \nplus(b,\ntimes(a,b)) \\ & = & \nplus(b,\ntimes(b,a)) \\ & = & \ntimes(b,\next(a)) \end{eqnarray*}$$ as needed.
5. We proceed by induction on $a$. For the base case, note that $$\ntimes(\zero,\nplus(b,c)) = \zero = \nplus(\zero,\zero) = \nplus(\ntimes(\zero,b),\ntimes(\zero,b)).$$ For the inductive step, suppose the result holds for some $a$. Now $$\begin{eqnarray*} \ntimes(\next(a),\nplus(b,c)) & = & \primrec{\const(\zero)}{\mu}(\next(a),\nplus(b,c)) \\ & = & \mu(a, \nplus(b,c), \primrec{\const(\zero)}{\mu}(a,\nplus(b,c))) \\ & = & \mu(a, \nplus(b,c), \ntimes(a,\nplus(b,c))) \\ & = & \nplus(\nplus(b,c), \ntimes(a,\nplus(b,c))) \\ & = & \nplus(\nplus(b,c),\nplus(\ntimes(a,b),\ntimes(a,c))) \\ & = & \nplus(\nplus(b,\ntimes(a,b)),\nplus(c,\ntimes(a,c))) \\ & = & \nplus(\ntimes(\next(a),b),\ntimes(\next(a),c)) \end{eqnarray*}$$ as needed.
6. Follows from (5) and (4).
7. (@@@)
</p></div>
</div>
