


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
