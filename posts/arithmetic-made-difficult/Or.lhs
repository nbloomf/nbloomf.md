---
title: Or
author: nbloomf
date: 2018-01-14
tags: arithmetic-made-difficult, literate-haskell
slug: or
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Or (
>   or, _test_or, main_or
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And

Finally, $\bor$.

:::::: definition ::
We define $\bor : \bool \times \bool \rightarrow \bool$ by $$\bor(p,q) = \bif{p}{\btrue}{\bif{q}{\btrue}{\ptrue}}.$$

In Haskell:

> or :: (Boolean b) => b -> b -> b
> or p q = ifThenElse p true (ifThenElse q true false)

::::::::::::::::::::

We can compute $\bor$ explicitly.

:::::: theorem :::::
<a name="def-or" />
We have
$$\begin{eqnarray*}
\bor(\btrue,\btrue)   & = & \btrue \\
\bor(\btrue,\bfalse)  & = & \btrue \\
\bor(\bfalse,\btrue)  & = & \btrue \\
\bor(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$

::: proof ::::::::::
(@@@)
::::::::::::::::::::

::: test :::::::::::

(@@@)

::::::::::::::::::::
::::::::::::::::::::

And $\bor$ satisfies the usual properties.

:::::: theorem :::::
The following hold for all $a,b,c \in \bool$.

1. $\bor(\btrue,a) = \bor(a,\btrue) = \btrue$.
2. $\bor(\bfalse,a) = \bor(a,\bfalse) = a$.
3. $\bor(p,\bnot(p)) = \btrue$.
4. $\bor(a,a) = a$.
5. $\bor(a,b) = \bor(b,a)$.
6. $\bor(\bor(a,b),c) = \bor(a,\bor(b,c))$.

::: proof ::::::::::
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
::::::::::::::::::::

::: test :::::::::::

> _test_or_true :: Test (Bool -> Bool)
> _test_or_true =
>   testName "or(true,p) == true" $
>   \p -> eq (or true p) true
> 
> 
> _test_or_false :: Test (Bool -> Bool)
> _test_or_false =
>   testName "or(false,p) == p" $
>   \p -> eq (or false p) p
> 
> 
> _test_or_not :: Test (Bool -> Bool)
> _test_or_not =
>   testName "or(p,not(p)) == true" $
>   \p -> eq (or p (not p)) true
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

::::::::::::::::::::
::::::::::::::::::::

Now $\bnot$, $\band$, and $\bor$ interact in the usual way.

:::::: theorem :::::
The following hold for all $a,b,c \in \bool$.

1. $\bnot(\band(a,b)) = \bor(\bnot(a),\bnot(b))$.
2. $\bnot(\bor(a,b)) = \band(\bnot(a),\bnot(b))$.
3. $\band(a,\bor(b,c)) = \bor(\band(a,b),\band(a,c))$.
4. $\bor(a,\band(b,c)) = \band(\bor(a,b),\bor(a,c))$.

::: proof ::::::::::
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
::::::::::::::::::::

::: test :::::::::::

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

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ on booleans is equivalent to an or.

:::::: theorem :::::
$$\bif{p}{\btrue}{q} = \bor(p,q).$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\btrue}{\btrue}{q} \\
 & = & \btrue \\
 & = & \bor(\btrue,q),
\end{eqnarray*}$$
and if $p = \bfalse we have
$$\begin{eqnarray*}
 &   & \bif{\bfalse}{\btrue}{q} \\
 & = & q \\
 & = & \bor(\bfalse,q)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_or :: (Equal a)
>   => a -> Test (Bool -> Bool -> Bool)
> _test_if_or _ =
>   testName "if(p,true,q) == or(p,q)" $
>   \p q -> eq (if p then true else q) (or p q)

::::::::::::::::::::
::::::::::::::::::::

$\bif{\ast}{\ast}{\ast}$ interacts with $\bor$.

:::::: theorem :::::
Let $A$ be a set with $a,b \in A$, and let $p,q \in \bool$. Then we have $$\bif{p}{a}{\bif{q}{a}{b}} = \bif{\bor(p,q)}{a}{b}.$$

::: proof ::::::::::
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{\bor(p,q)}{a}{b} \\
 & = & \bif{\btrue}{a}{b} \\
 & = & a
 & = & \bif{\btrue}{a}{\bif{q}{a}{b}} \\
 & = & \bif{p}{a}{\bif{q}{a}{b}}
\end{eqnarray*}$$
as needed, and if $p = \bfalse$ we have
$$\begin{eqnarray*}
 &   & \bif{\bor(p,q)}{a}{b} \\
 & = & \bif{q}{a}{b} \\
 & = & \bif{\bfalse}{a}{\bif{q}{a}{b}} \\
 & = & \bif{p}{a}{\bif{q}{a}{b}}
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_if_or_nest :: (Equal a)
>   => a -> Test (a -> a -> Bool -> Bool -> Bool)
> _test_if_or_nest _ =
>   testName "if(or(p,q),a,b) == if(p,a,if(q,a,b))" $
>   \a b p q -> eq
>     (if or p q then a else b)
>     (if p then a else if q then a else b)

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_or ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a
>   , Boolean b, Arbitrary b, Show b, Equal b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_or p x size num = do
>   testLabel0 "Bool"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
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
>   runTest args (_test_if_or x)
>   runTest args (_test_if_or_nest x)

Main:

> main_or :: IO ()
> main_or = _test_or (true :: Bool) (true :: Bool) 20 100
