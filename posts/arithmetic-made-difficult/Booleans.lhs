---
title: Booleans
author: nbloomf
date: 2014-04-01
tags: arithmetic-made-difficult, literate-haskell
slug: booleans
---

> module Booleans
>   ( Bool(..), not, and, or, impl, ifThenElse
>   , Equal, eq
>   , _test_boolean, main_boolean
> 
>   , Test, runTest, testName, testLabel, withTypeOf, TypeName(..)
>   , testLabel1, testLabel2, testLabel3
> 
>   , module Prelude
>   , module Test.QuickCheck
>   , module Test.QuickCheck.Test
> ) where
> 
> import Prelude
>   ( Show(show), IO, Bool(..), Int, Maybe(..), Either(..), id, undefined, concat
>   , putStrLn, (>>), return, (++), String, (.), ($), Integer, const, uncurry
>   )
> import Test.QuickCheck
>   ( Testable(..), Args(..), Arbitrary(..), CoArbitrary(..)
>   , quickCheckWithResult, stdArgs, variant
>   )
> import Test.QuickCheck.Test (isSuccess)
> import Text.Show.Functions
> import System.Exit

Before we think about numbers or writing programs, let's start by nailing down some important ideas about truth values. In math there can be a kind of other-worldness about True and False, since they live in the "metalanguage" of mathematical logic rather than the "object language" of whatever we are studying. But it will turn out to be useful to algebraify the truth values themselves.

:::: definition ::::
[](#def-bool) We define a set $\bool = \{\btrue,\bfalse\}$. The elements of $\bool$ are called *booleans* or *truth values*.
::::::::::::::::::::

We can model $\bool$ using the built in Haskell type ``Bool``, which looks something like this.

```haskell
data Bool = True | False
```

We also define the usual logical operators in turn. First, $\bnot$:

:::: definition ::::
[](#def-not) We define $\bnot : \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\bnot(\btrue)  & = & \bfalse \\
\bnot(\bfalse) & = & \btrue.
\end{eqnarray*}$$

In Haskell:

> not :: Bool -> Bool
> not True  = False
> not False = True

::::::::::::::::::::

Where $\bnot$ is an involution.

:::: theorem ::::
[](#not-involution)
For all $a \in \bool$ we have $\bnot(\bnot(a)) = a$.

::: proof :::
If $a = \btrue$ we have $$\bnot(\bnot(\btrue)) = \bnot(\bfalse) = \btrue,$$ and if $a = \bfalse$, we have $$\bnot(\bnot(\bfalse)) = \bnot(\btrue) = \bfalse$$ as claimed.
:::::::::::::

::: test :::

> _test_not_involutive :: Test (Bool -> Bool)
> _test_not_involutive =
>   testName "not(not(p)) == p" $
>   \p -> eq (not (not p)) p

::::::::::::
:::::::::::::::::

Next, $\band$:

<div class="result">
<div class="defn"><p><a name="def-and" />
We define a map $\band : \bool \times \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\band(\btrue,\btrue)   & = & \btrue \\
\band(\btrue,\bfalse)  & = & \bfalse \\
\band(\bfalse,\btrue)  & = & \bfalse \\
\band(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$

In Haskell: 

> and :: Bool -> Bool -> Bool
> and True True = True
> and _    _    = False

</p></div>
</div>

And $\band$ satisfies the usual properties.

<div class="result">
<div class="thm"><p>
The following hold for all $a,b,c \in \bool$.

1. $\band(\bfalse,a) = \band(a,\bfalse) = \bfalse$.
2. $\band(\btrue,a) = \band(a,\btrue) = a$.
3. $\band(a,\bnot(a)) = \bfalse$.
4. $\band(a,a) = a$.
5. $\band(a,b) = \band(b,a)$.
6. $\band(\band(a,b),c) = \band(a,\band(b,c))$.
</p></div>

<div class="proof"><p>
1. If $a = \btrue$ we have $$\band(\bfalse,\btrue) = \bfalse = \band(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
2. If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\btrue,\bfalse) = \bfalse = \band(\bfalse,\btrue)$$ as claimed.
3. If $a = \btrue$, we have $\band(\btrue,\bnot(\btrue)) = \band(\btrue,\bfalse) = \bfalse,$$ and if $a = \bfalse$, we have $$\band(\bfalse,\bnot(\bfalse)) = \bfalse$$ as claimed.
4. If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
5. If $a = \btrue$ we have $$\band(\btrue,b) = b = \band(b,\btrue),$$ and if $a = \bfalse$ we have $$\band(\bfalse,b) = \bfalse = \band(b,\bfalse)$$ as claimed.
6. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\btrue,b),c) \\
 & = & \band(b,c) \\
 & = & \band(\btrue,\band(b,c)) \\
 & = & \band(a,\band(b,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(\band(a,b),c) \\
 & = & \band(\band(\bfalse,b),c) \\
 & = & \band(\bfalse,c) \\
 & = & \bfalse \\
 & = & \band(\bfalse,\band(b,c))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_and_false :: Test (Bool -> Bool)
> _test_and_false =
>   testName "and(false,p) == false" $
>   \p -> eq (and False p) False
> 
> 
> _test_and_true :: Test (Bool -> Bool)
> _test_and_true =
>   testName "and(true,p) == p" $
>   \p -> eq (and True p) p
> 
> 
> _test_and_not :: Test (Bool -> Bool)
> _test_and_not =
>   testName "and(p,not(p)) == false" $
>   \p -> eq (and p (not p)) False
> 
> 
> _test_and_idempotent :: Test (Bool -> Bool)
> _test_and_idempotent =
>   testName "and(p,p) == p" $
>   \p -> eq (and p p) p
> 
> 
> _test_and_commutative :: Test (Bool -> Bool -> Bool)
> _test_and_commutative =
>   testName "and(p,q) == and(q,p)" $
>   \p q -> eq (and p q) (and q p)
> 
> 
> _test_and_associative :: Test (Bool -> Bool -> Bool -> Bool)
> _test_and_associative =
>   testName "and(and(p,q),r) == and(p,and(q,r))" $
>   \p q r -> eq (and (and p q) r) (and p (and q r))

</p></div>
</div>

Finally, $\bor$:

<div class="result">
<div class="defn"><p><a name="def-or" />
We define $\bor : \bool \times \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\bor(\btrue,\btrue)   & = & \btrue \\
\bor(\btrue,\bfalse)  & = & \btrue \\
\bor(\bfalse,\btrue)  & = & \btrue \\
\bor(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$

In Haskell:

> or :: Bool -> Bool -> Bool
> or False False = False
> or _     _     = True

</p></div>
</div>

And $\bor$ satisfies the usual properties.

<div class="result">
<div class="thm"><p>
The following hold for all $a,b,c \in \bool$.

1. $\bor(\btrue,a) = \bor(a,\btrue) = \btrue$.
2. $\bor(\bfalse,a) = \bor(a,\bfalse) = a$.
3. $\bor(p,\bnot(p)) = \btrue$.
4. $\bor(a,a) = a$.
5. $\bor(a,b) = \bor(b,a)$.
6. $\bor(\bor(a,b),c) = \bor(a,\bor(b,c))$.
</p></div>

<div class="proof"><p>
1. If $a = \btrue$, we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\bor(\btrue,\bfalse) = \btrue = \bor(\bfalse,\btrue)$$ as claimed.
2. If $a = \btrue$, we have $$\bor(\bfalse,\btrue) = \btrue = \bor(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
3. If $a = \btrue$, we have $$\bor(\btrue,\bnot(\btrue)) = \btrue,$$ and if $a = \bfalse$ we have $$\bor(\bfalse,\bnot(\bfalse)) = \bor(\bfalse,\btrue) = \btrue$$ as claimed.
4. If $a = \btrue$ we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ then $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
5. If $a = \btrue$ we have $$\bor(\btrue,b) = \btrue = \bor(b,\btrue),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,b) = b = \bor(b,\bfalse)$$ as claimed.
6. If $a = \btrue$ we have
$$\begin{eqnarray*}
 &   & \bor(\bor(a,b),c) \\
 & = & \bor(\bor(\btrue,b),c) \\
 & = & \bor(\btrue,c) \\
 & = & \btrue \\
 & = & \bor(\btrue,\bor(b,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bor(\bor(a,b),c) \\
 & = & \bor(\bor(\bfalse,b),c) \\
 & = & \bor(b,c) \\
 & = & \bor(\bfalse,\bor(b,c))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_or_true :: Test (Bool -> Bool)
> _test_or_true =
>   testName "or(true,p) == true" $
>   \p -> eq (or True p) True
> 
> 
> _test_or_false :: Test (Bool -> Bool)
> _test_or_false =
>   testName "or(false,p) == p" $
>   \p -> eq (or False p) p
> 
> 
> _test_or_not :: Test (Bool -> Bool)
> _test_or_not =
>   testName "or(p,not(p)) == true" $
>   \p -> eq (or p (not p)) True
> 
> 
> _test_or_idempotent :: Test (Bool -> Bool)
> _test_or_idempotent =
>   testName "or(p,p) == p" $
>   \p -> eq (or p p) p
> 
> 
> _test_or_commutative :: Test (Bool -> Bool -> Bool)
> _test_or_commutative =
>   testName "or(p,q) == or(q,p)" $
>   \p q -> eq (or p q) (or q p)
> 
> 
> _test_or_associative :: Test (Bool -> Bool -> Bool -> Bool)
> _test_or_associative =
>   testName "or(or(p,q),r) == or(p,or(q,r))" $
>   \p q r -> eq (or (or p q) r) (or p (or q r))

</p></div>
</div>

Now $\bnot$, $\band$, and $\bor$ interact in the usual way.

<div class="result">
<div class="thm"><p>
The following hold for all $a,b,c \in \bool$.

1. $\bnot(\band(a,b)) = \bor(\bnot(a),\bnot(b))$.
2. $\bnot(\bor(a,b)) = \band(\bnot(a),\bnot(b))$.
3. $\band(a,\bor(b,c)) = \bor(\band(a,b),\band(a,c))$.
4. $\bor(a,\band(b,c)) = \band(\bor(a,b),\bor(a,c))$.
</p></div>

<div class="proof"><p>
1. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bnot(\band(a,b)) \\
 & = & \bnot(\band(\btrue,b)) \\
 & = & \bnot(b) \\
 & = & \bor(\bfalse,\bnot(b)) \\
 & = & \bor(\bnot(\btrue),\bnot(b)) \\
 & = & \bor(\bnot(a),\bnot(b))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bnot(\band(a,b)) \\
 & = & \bnot(\band(\bfalse,b)) \\
 & = & \bnot(\bfalse) \\
 & = & \btrue \\
 & = & \bor(\btrue,\bnot(b)) \\
 & = & \bor(\bnot(\bfalse),\bnot(b)) \\
 & = & \bor(\bnot(a),\bnot(b))
\end{eqnarray*}$$
as claimed.
2. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bnot(\bor(a,b)) \\
 & = & \bnot(\bor(\btrue,b)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse \\
 & = & \band(\bfalse,\bnot(b)) \\
 & = & \band(\bnot(\btrue),\bnot(b)) \\
 & = & \band(\bnot(a),\bnot(b))
\end{eqnarray*}$$
as claimed. If $b = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bnot(\bor(a,b)) \\
 & = & \bnot(\bor(\bfalse,b)) \\
 & = & \bnot(b) \\
 & = & \band(\btrue,\bnot(b)) \\
 & = & \band(\bnot(\bfalse),\bnot(b)) \\
 & = & \band(\bnot(a),\bnot(b))
\end{eqnarray*}$$
as claimed.
3. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \band(a,\bor(b,c)) \\
 & = & \band(\btrue,\bor(b,c)) \\
 & = & \bor(b,c) \\
 & = & \bor(\band(\btrue,b),\band(\btrue,c)) \\
 & = & \bor(\band(a,b),\band(a,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \band(a,\bor(b,c)) \\
 & = & \band(\bfalse,\bor(b,c)) \\
 & = & \bfalse \\
 & = & \bor(\bfalse,\bfalse) \\
 & = & \bor(\band(\bfalse,b),\band(\bfalse,c)) \\
 & = & \bor(\band(a,b),\band(a,c))
\end{eqnarray*}$$
as claimed.
4. If $a = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bor(a,\band(b,c)) \\
 & = & \bor(\btrue,\band(b,c)) \\
 & = & \btrue \\
 & = & \band(\btrue,\btrue) \\
 & = & \band(\bor(\btrue,b),\bor(\btrue,c)) \\
 & = & \band(\bor(a,b),\bor(a,c))
\end{eqnarray*}$$
as claimed. If $a = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bor(a,\band(b,c)) \\
 & = & \bor(\bfalse,\band(b,c)) \\
 & = & \band(b,c) \\
 & = & \band(\bor(\bfalse,b),\bor(\bfalse,c)) \\
 & = & \band(\bor(a,b),\bor(a,c))
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_not_and :: Test (Bool -> Bool -> Bool)
> _test_not_and =
>   testName "not(and(p,q)) == or(not(p),not(q))" $
>   \p q -> eq (not (and p q)) (or (not p) (not q))
> 
> 
> _test_not_or :: Test (Bool -> Bool -> Bool)
> _test_not_or =
>   testName "not(or(p,q)) == and(not(p),not(q))" $
>   \p q -> eq (not (or p q)) (and (not p) (not q))
> 
> 
> _test_and_or :: Test (Bool -> Bool -> Bool -> Bool)
> _test_and_or =
>   testName "and(p,or(q,r)) == or(and(p,q),and(p,r))" $
>   \p q r -> eq (and p (or q r)) (or (and p q) (and p r))
> 
> 
> _test_or_and :: Test (Bool -> Bool -> Bool -> Bool)
> _test_or_and =
>   testName "or(p,and(q,r)) == and(or(p,q),or(p,r))" $
>   \p q r -> eq (or p (and q r)) (and (or p q) (or p r))

</p></div>
</div>

Implication on booleans:

<div class="result">
<div class="defn"><p>
We define $\bimpl : \bool \times \bool \rightarrow \bool$ by $$\bimpl(p,q) = \bor(\bnot(p),q).$$

In Haskell:

> impl :: Bool -> Bool -> Bool
> impl p q = or (not p) q

</p></div>
</div>

And implication has its own properties.

<div class="result">
<div class="thm"><p>
For all $p,q,r,s \in \bool$ we have the following.

1. $\bimpl(\bfalse,p) = \btrue$.
2. $\bimpl(\btrue,p) = p$.
3. $\bimpl(p,p)$.
4. $\bor(\bimpl(p,q),\bimpl(q,p))$.
5. $\bimpl(p,\bimpl(q,r)) = \bimpl(q,\bimpl(p,r))$.
6. $\bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r)))$.
7. $\bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r)))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \bimpl(\bfalse,p) \\
 & = & \bor(\bnot(\bfalse),p) \\
 & = & \bor(\btrue,p) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,p) \\
 & = & \bor(\bnot(\btrue),p) \\
 & = & \bor(\bfalse,p) \\
 & = & p
\end{eqnarray*}$$
as claimed.
3. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\btrue,\btrue) \\
 & = & \bor(\bnot(\btrue),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
4. We have
$$\begin{eqnarray*}
 &   & \bor(\bimpl(p,q),\bimpl(q,p)) \\
 & = & \bor(\bor(\bnot(p),q),\bor(\bnot(q),p)) \\
 & = & \bor(\bnot(p),\bor(q,\bor(\bnot(q),p))) \\
 & = & \bor(\bnot(p),\bor(\bor(q,\bnot(q)),p)) \\
 & = & \bor(\bnot(p),\bor(\btrue,p)) \\
 & = & \bor(\bnot(p),\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
5. We have
$$\begin{eqnarray*}
 &   & \bimpl(p,\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bimpl(q,r)) \\
 & = & \bor(\bnot(p),\bor(\bnot(q),r)) \\
 & = & \bor(\bor(\bnot(p),\bnot(q)),r) \\
 & = & \bor(\bor(\bnot(q),\bnot(p)),r) \\
 & = & \bor(\bnot(q),\bor(\bnot(p),r)) \\
 & = & \bor(\bnot(q),\bimpl(p,r)) \\
 &   & \bimpl(q,\bimpl(p,r))
\end{eqnarray*}$$
as claimed.
6. We have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,q),\bimpl(\bimpl(q,r),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bimpl(q,r)),\bimpl(p,r))) \\
 & = & \bimpl(\bor(\bnot(p),q),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\bnot(\bor(\bnot(p),q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(\bnot(\bnot(p)),\bnot(q))),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\bnot(\bor(\bnot(q),r)),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(\bnot(\bnot(q)),\bnot(r))),\bor(\bnot(p),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(p),r))) \\
 & = & Q.
\end{eqnarray*}$$
If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\bfalse),r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\btrue,r))) \\
 & = & \bor(\band(p,\bnot(q)),\bor(\band(q,\bnot(r)),\btrue)) \\
 & = & \bor(\band(p,\bnot(q)),\btrue) \\
 & = & \btrue.
\end{eqnarray*}$$
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & Q \\
 & = & \bor(\band(\btrue,\bnot(q)),\bor(\band(q,\bnot(r)),\bor(\bnot(\btrue),r))) \\
 & = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),\bor(\bfalse,r))) \\
 & = & \bor(\bnot(q),\bor(\band(q,\bnot(r)),r)) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\bor(\bnot(r),r))) \\
 & = & \bor(\bnot(q),\band(\bor(q,r),\btrue)) \\
 & = & \bor(\bnot(q),\bor(q,r)) \\
 & = & \bor(\bor(\bnot(q),q),r) \\
 & = & \bor(\btrue,r) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
7. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 & = & \bimpl(\bimpl(\bfalse,\bimpl(q,r)),\bimpl(\bimpl(\bfalse,q),\bimpl(\bfalse,r))) \\
 & = & \bimpl(\btrue,\bimpl(\btrue,\btrue)) \\
 & = & \bimpl(\btrue,\btrue) \\
 & = & \btrue.
\end{eqnarray*}$$
Suppose instead that $p = \btrue$. Now
$$\begin{eqnarray*}
 &   & \bimpl(\bimpl(p,\bimpl(q,r)),\bimpl(\bimpl(p,q),\bimpl(p,r))) \\
 & = & \bimpl(\bimpl(\btrue,\bimpl(q,r)),\bimpl(\bimpl(\btrue,q),\bimpl(\btrue,r))) \\
 & = & \bimpl(\bimpl(q,r),\bimpl(\bimpl(q,r)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_impl_false :: Test (Bool -> Bool)
> _test_impl_false =
>   testName "impl(false,p) == true" $
>   \p -> eq (impl False p) True
> 
> 
> _test_impl_true :: Test (Bool -> Bool)
> _test_impl_true =
>   testName "impl(true,p) == p" $
>   \p -> eq (impl True p) p
> 
> 
> _test_impl_reflexive :: Test (Bool -> Bool)
> _test_impl_reflexive =
>   testName "impl(p,p) == true" $
>   \p -> eq (impl p p) True
> 
> 
> _test_impl_total :: Test (Bool -> Bool -> Bool)
> _test_impl_total =
>   testName "or(impl(p,q),impl(q,p)) == true" $
>   \p q -> eq (or (impl p q) (impl q p)) True
> 
> 
> _test_impl_antecedents_commute :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_antecedents_commute =
>   testName "impl(p,impl(q,r)) == impl(q,impl(p,r))" $
>   \p q r -> eq (impl p (impl q r)) (impl q (impl p r))
> 
> 
> _test_impl_transitive :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_transitive =
>   testName "impl(impl(p,q),impl(impl(q,r),impl(p,r)))" $
>   \p q r -> impl (impl p q) (impl (impl q r) (impl p r))
> 
> 
> _test_impl_distributive :: Test (Bool -> Bool -> Bool -> Bool)
> _test_impl_distributive =
>   testName "impl(impl(p,impl(q,r)),impl(impl(p,q),impl(p,r)))" $
>   \p q r -> impl (impl p (impl q r)) (impl (impl p q) (impl p r))

</p></div>
</div>

$\bimpl$ interacts with $\band$.

<div class="result">
<div class="thm"><p>
For all $p,q,r,s \in \bool$, if $\bimpl(p,r)$ and $\bimpl(q,s)$, then $\bimpl(\band(p,q),\band(r,s))$.
</p></div>

<div class="proof"><p>
If $p = \bfalse$, then
$$\begin{eqnarray*}
 &   & \bimpl(\band(p,q),\band(r,s)) \\
 & = & \bimpl(\band(\bfalse,q),\band(r,s)) \\
 & = & \bimpl(\bfalse,\band(r,s))
 & = & \btrue.
\end{eqnarray*}$$
Similarly if $q = \bfalse$. Suppose then that $p = q = \btrue$. Now
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \bimpl(p,r) \\
 & = & \bimpl(\btrue,r) \\
 & = & r,
\end{eqnarray*}$$
and similarly $s = \btrue$. Then
$$\begin{eqnarray*}
 &   & \bimpl(\band(p,q),\band(r,s)) \\
 & = & \bimpl(\band(\btrue,\btrue),\band(\btrue,\btrue)) \\
 & = & \bimpl(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_impl_and_compatible :: Test (Bool -> Bool -> Bool -> Bool -> Bool)
> _test_impl_and_compatible =
>   testName "if and(impl(p,r),impl(q,s)) then impl(and(p,q),and(r,s))" $
>   \p q r s -> if and (impl p r) (impl q s)
>     then impl (and p q) (and r s)
>     else True

</p></div>
</div>

Wow, that was tedious! But we only have to do it once. :)

Next we nail down conditional expressions.

<div class="result">
<div class="defn"><p><a name="def-if" />
Let $A$ be a set. We define a map $\mathsf{if} : \bool \times A \times A \rightarrow A$ by
$$\begin{eqnarray*}
\bif{\btrue}{u}{v}  & = & u \\
\bif{\bfalse}{u}{v} & = & v.
\end{eqnarray*}$$

In Haskell:

> ifThenElse :: Bool -> a -> a -> a
> ifThenElse True  x _ = x
> ifThenElse False _ y = y

</p></div>
</div>

Now $\bif{\ast}{\ast}{\ast}$ also satisfies some useful properties; for instance, it interacts with not in the first argument:

<div class="result">
<div class="thm"><p><a name="thm-ifnot" />
Let $A$ be a set with $p \in \bool$ and $a,b \in A$. We have $$\bif{\bnot(p)}{a}{b} = \bif{p}{b}{a}.$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\bnot(p)}{a}{b} \\
 & = & \bif{\bnot(\btrue)}{a}{b} \\
 & = & \bif{\bfalse}{a}{b} \\
 & = & b \\
 & = & \bif{\btrue}{b}{a} \\
 & = & \bif{p}{b}{a},
\end{eqnarray*}$$
and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{\bnot(p)}{a}{b} \\
 & = & \bif{\bnot(\bfalse)}{a}{b} \\
 & = & \bif{\btrue}{a}{b} \\
 & = & a \\
 & = & \bif{\bfalse}{b}{a} \\
 & = & \bif{p}{b}{a},
\end{eqnarray*}$$
as needed.
</p></div>

<div class="test"><p>

> _test_if_not :: (Equal a) => a -> Test (Bool -> a -> a -> Bool)
> _test_if_not _ =
>   testName "if(not(p),a,b) == if(p,b,a)" $
>   \p a b -> eq (ifThenElse (not p) a b) (ifThenElse p b a)

</p></div>
</div>

If interacts with function application:

<div class="result">
<div class="thm"><p><a name="thm-iffunc" />
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $p \in \bool$ and $u,v \in A$, we have $$f(\bif{p}{u}{v}) = \bif{p}{f(u)}{f(v)}.$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\btrue}{u}{v}) \\
 & = & f(u) \\
 & = & \bif{\btrue}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\bfalse}{u}{v}) \\
 & = & f(v) \\
 & = & \bif{\bfalse}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_func :: (Equal a)
>   => a -> Test ((a -> a) -> Bool -> a -> a -> Bool)
> _test_if_func _ =
>   testName "f(if(p,a,b)) == if(p,f(a),f(b))" $
>   \f p a b -> eq (f (ifThenElse p a b)) (ifThenElse p (f a) (f b))

</p></div>
</div>

Nested $\bif{\ast}{\ast}{\ast}$s commute (sort of).

<div class="result">
<div class="thm"><p><a name="thm-ifnest" />
Let $A$ be a set with $p,q \in \bool$ and $a,b,c,d \in A$. Then we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}.
\end{eqnarray*}$$
</p></div>

<div class="proof"><p>
We have four possibilities for $(p,q)$. If $p = \btrue$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\btrue}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{a}{b} \\
 & = & a \\
 & = & \bif{\btrue}{a}{c} \\
 & = & \bif{\btrue}{\bif{\btrue}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \btrue$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{a}{b} \\
 & = & b \\
 & = & \bif{\btrue}{b}{d} \\
 & = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\btrue}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\btrue}{c}{d}} \\
 & = & \bif{\btrue}{c}{d} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\bfalse}{c}{d}} \\
 & = & \bif{\bfalse}{c}{d} \\
 & = & d \\
 & = & \bif{\bfalse}{b}{d} \\
 & = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\bfalse}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_nest :: (Equal a)
>   => a -> Test (Bool -> Bool -> a -> a -> a -> a -> Bool)
> _test_if_nest _ =
>   testName "if(p,if(q,a,b),if(q,c,d)) == if(q,if(p,a,c),if(p,b,d))" $
>   \p q a b c d ->
>     eq
>       (ifThenElse p (ifThenElse q a b) (ifThenElse q c d))
>       (ifThenElse q (ifThenElse p a c) (ifThenElse p b d))

</p></div>
</div>

Nested ifs on the same boolean can be pruned.

<div class="result">
<div class="thm"><p><a name="thm-ifprune" />
Let $A$ be a set with $p \in \bool$ and $a,b,c \in A$. We have the following.

1. $\bif{p}{\bif{p}{a}{b}}{c} = \bif{p}{a}{c}$
2. $\bif{p}{a}{\bif{p}{b}{c}} = \bif{p}{a}{c}$
</p></div>

<div class="proof"><p>
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{p}{\bif{\btrue}{a}{b}}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{\bfalse}{\bif{\bfalse}{a}{b}}{c} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed.
2. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{\btrue}{a}{\bif{p}{b}{c}} \\
 & = & a \\
 & = & \bif{\btrue}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed, and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{p}{a}{\bif{\bfalse}{b}{c}} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_prune :: (Equal a)
>   => a -> Test (Bool -> a -> a -> a -> Bool)
> _test_if_prune _ =
>   testName "if(p,if(p,a,b),c) == if(p,a,c) == if(p,a,if(p,b,c))" $
>   \p a b c ->
>     and
>       (eq (ifThenElse p (ifThenElse p a b) c) (ifThenElse p a c))
>       (eq (ifThenElse p a (ifThenElse p b c)) (ifThenElse p a c))

</p></div>
</div>

$\bif{\ast}{\ast}{\ast}$ is sort of commutative.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $p,q \in \bool$ and $a,b \in A$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & \bif{q}{a}{\bif{p}{a}{b}}.
\end{eqnarray*}$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & a \\
 & = & \bif{q}{a}{a} \\
 & = & \bif{q}{a}{\bif{p}{a}{c}}
\end{eqnarray*}$$
as claimed. Likewise, the equality holds if $q = \btrue$. Suppose then that $p = q = \bfalse$; now
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & \bif{q}{a}{b} \\
 & = & b \\
 & = & \bif{p}{a}{b} \\
 & = & \bif{q}{a}{\bif{p}{a}{b}}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_commute_left :: (Equal a)
>   => a -> Test (Bool -> Bool -> a -> a -> Bool)
> _test_if_commute_left _ =
>   testName "if(p,a,if(q,a,b)) == if(q,a,if(p,a,b))" $
>   \p q a b -> eq
>     (ifThenElse p a (ifThenElse q a b))
>     (ifThenElse q a (ifThenElse p a b))

</p></div>
</div>


Equality
--------

Now that we've algebraified truth values, we will also algebraify equality. Typically I think of equality (as in the $=$ symbol) as a metalanguage expression. Sure, we can define a relation that captures equality on a given set, but really equality is a "logical" thing, not a "mathematical" one. We'll express this using a type class in Haskell like so.

> class Equal a where
>   eq :: a -> a -> Bool
> 
>   neq :: a -> a -> Bool
>   neq x y = not (eq x y)

(Why not use the built in `Eq` class? No good reason.) For example, here is the ``Equal`` instance for ``Bool``:

> instance Equal Bool where
>   eq True  True  = True
>   eq True  False = False
>   eq False True  = False
>   eq False False = True
> 
> instance Equal () where
>   eq () () = True
> 
> instance Equal a => Equal (Maybe a) where
>   eq Nothing  Nothing  = True
>   eq Nothing  (Just _) = False
>   eq (Just _) Nothing  = False
>   eq (Just x) (Just y) = eq x y
> 
> instance (Equal a, Equal b) => Equal (a,b) where
>   eq (a1,b1) (a2,b2) = and (eq a1 a2) (eq b1 b2)
> 
> instance (Equal a, Equal b) => Equal (Either a b) where
>   eq (Left a1)  (Left a2)  = eq a1 a2
>   eq (Left a1)  (Right b2) = False
>   eq (Right b1) (Left a2)  = False
>   eq (Right b1) (Right b2) = eq b1 b2


Testing
-------

One of our main uses for ``Bool`` will be checking the results of tests, so this is as good a place as any to introduce a couple of QuickCheck helper functions for this.

> type Test prop = (String, prop)
> 
> testName :: String -> prop -> Test prop
> testName name prop = (name, prop)
> 
> runTest :: Testable prop => Args -> Test prop -> IO ()
> runTest args (name, prop) = do
>   putStrLn ("\x1b[1;34m" ++ name ++ "\x1b[0;39;49m")
>   result <- quickCheckWithResult args prop
>   if isSuccess result
>     then return ()
>     else putStrLn (show result) >> exitFailure
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\n\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
> 
> testLabel1 :: (TypeName a) => String -> a -> IO ()
> testLabel1 str a = testLabel $ concat
>   [ str, ": ", typeName a ]
> 
> testLabel2 :: (TypeName a, TypeName b) => String -> a -> b -> IO ()
> testLabel2 str a b = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b ]
> 
> testLabel3 :: (TypeName a, TypeName b, TypeName c) => String -> a -> b -> c -> IO ()
> testLabel3 str a b c = testLabel $ concat
>   [ str, ": ", typeName a, ", ", typeName b, ", ", typeName c ]
>
> 
> withTypeOf :: a -> a -> a
> withTypeOf x _ = x
> 
> class TypeName t where
>   typeName :: t -> String
> 
> instance TypeName Bool where
>   typeName _ = "Bool"

And the suite:

> _test_boolean :: (Equal a, Arbitrary a, CoArbitrary a, Show a)
>   => a -> Int -> Int -> IO ()
> _test_boolean x size num = do
>   testLabel "Bool"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args _test_not_involutive
> 
>   runTest args _test_and_false
>   runTest args _test_and_true
>   runTest args _test_and_not
>   runTest args _test_and_idempotent
>   runTest args _test_and_commutative
>   runTest args _test_and_associative
> 
>   runTest args _test_or_true
>   runTest args _test_or_false
>   runTest args _test_or_not
>   runTest args _test_or_idempotent
>   runTest args _test_or_commutative
>   runTest args _test_or_associative
> 
>   runTest args _test_not_and
>   runTest args _test_not_or
>   runTest args _test_and_or
>   runTest args _test_or_and
> 
>   runTest args _test_impl_false
>   runTest args _test_impl_true
>   runTest args _test_impl_reflexive
>   runTest args _test_impl_total
>   runTest args _test_impl_antecedents_commute
>   runTest args _test_impl_transitive
>   runTest args _test_impl_distributive
>   runTest args _test_impl_and_compatible
> 
>   runTest args (_test_if_not x)
>   runTest args (_test_if_func x)
>   runTest args (_test_if_nest x)
>   runTest args (_test_if_prune x)
>   runTest args (_test_if_commute_left x)

Main:

> main_boolean :: IO ()
> main_boolean = _test_boolean True 20 100
