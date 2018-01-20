---
title: Or
author: nbloomf
date: 2018-01-17
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
Note that
$$\begin{eqnarray*}
 &   & \bor(\btrue,\btrue) \\
 & = & \bif{\btrue}{\btrue}{\bif{\btrue}{\btrue}{\bfalse}} \\
 & = & \btrue,
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \bor(\btrue,\bfalse) \\
 & = & \bif{\btrue}{\btrue}{\bif{\bfalse}{\btrue}{\bfalse}} \\
 & = & \btrue,
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \bor(\bfalse,\btrue) \\
 & = & \bif{\bfalse}{\btrue}{\bif{\btrue}{\btrue}{\bfalse}} \\
 & = & \bif{\bfalse}{\btrue}{\btrue} \\
 & = & \btrue,
\end{eqnarray*}$$
and that
$$\begin{eqnarray*}
 &   & \bor(\bfalse,\bfalse) \\
 & = & \bif{\bfalse}{\btrue}{\bif{\bfalse}{\btrue}{\bfalse}} \\
 & = & \bif{\bfalse}{\btrue}{\bfalse} \\
 & = & \bfalse,
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_true_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_or_true_true p =
>   testName "or(true,true) == true" $
>   eq (or true true) (true `withTypeOf` p)
> 
> 
> _test_or_true_false :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_or_true_false p =
>   testName "or(true,false) == true" $
>   eq (or true false) (true `withTypeOf` p)
> 
> 
> _test_or_false_true :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_or_false_true p =
>   testName "or(false,true) == true" $
>   eq (or false true) (true `withTypeOf` p)
> 
> 
> _test_or_false_false :: (Boolean b, Equal b)
>   => b -> Test Bool
> _test_or_false_false p =
>   testName "or(false,false) == false" $
>   eq (or false false) (false `withTypeOf` p)

::::::::::::::::::::
::::::::::::::::::::

$\btrue$ absorbs under $\bor$.

:::::: theorem :::::
For all $a \in \bool$, we have $$\bor(\btrue,a) = \bor(a,\btrue) = \btrue.$$

::: proof ::::::::::
If $a = \btrue$, we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\bor(\btrue,\bfalse) = \btrue = \bor(\bfalse,\btrue)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_true :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_or_true b =
>   testName "or(true,p) == true" $
>   \p -> eq (or true p) (true `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

$\bfalse$ is neutral under $\bor$.

:::::: theorem :::::
For all $a \in \bool$, we have $$\bor(\bfalse,a) = \bor(a,\bfalse) = a.$$

::: proof ::::::::::
If $a = \btrue$, we have $$\bor(\bfalse,\btrue) = \btrue = \bor(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_false :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_or_false _ =
>   testName "or(false,p) == p" $
>   \p -> eq (or false p) p

::::::::::::::::::::
::::::::::::::::::::

$\bor$ interacts with $\bnot$.

:::::: theorem :::::
For all $a \in \bool$, we have $\bor(p,\bnot(p)) = \btrue$.

::: proof ::::::::::
If $a = \btrue$, we have $$\bor(\btrue,\bnot(\btrue)) = \btrue,$$ and if $a = \bfalse$ we have $$\bor(\bfalse,\bnot(\bfalse)) = \bor(\bfalse,\btrue) = \btrue$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_not :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_or_not b =
>   testName "or(p,not(p)) == true" $
>   \p -> eq (or p (not p)) (true `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

$\bor$ is idempotent.

:::::: theorem :::::
For all $a \in \bool$, we have $\bor(a,a) = a$.

::: proof ::::::::::
If $a = \btrue$ we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ then $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_idempotent :: (Boolean b, Equal b)
>   => b -> Test (b -> Bool)
> _test_or_idempotent _ =
>   testName "or(p,p) == p" $
>   \p -> eq (or p p) p

::::::::::::::::::::
::::::::::::::::::::

$\bor$ is commutative.

:::::: theorem :::::
For all $a,b \in \bool$, we have $\bor(a,b) = \bor(b,a)$.

::: proof ::::::::::
If $a = \btrue$ we have $$\bor(\btrue,b) = \btrue = \bor(b,\btrue),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,b) = b = \bor(b,\bfalse)$$ as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_or_commutative :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_or_commutative _ =
>   testName "or(p,q) == or(q,p)" $
>   \p q -> eq (or p q) (or q p)

::::::::::::::::::::
::::::::::::::::::::

$\bor$ is associative.

:::::: theorem :::::
For all $a,b,c \in \bool$, we have $$\bor(\bor(a,b),c) = \bor(a,\bor(b,c)).$$

::: proof ::::::::::
If $a = \btrue$ we have
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

> _test_or_associative :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_or_associative _ =
>   testName "or(or(p,q),r) == or(p,or(q,r))" $
>   \p q r -> eq (or (or p q) r) (or p (or q r))

::::::::::::::::::::
::::::::::::::::::::

DeMorgan's laws hold for $\bor$, $\band$, and $\bnot$.

:::::: theorem :::::
The following hold for all $a,b,c \in \bool$.

1. $\bnot(\band(a,b)) = \bor(\bnot(a),\bnot(b))$.
2. $\bnot(\bor(a,b)) = \band(\bnot(a),\bnot(b))$.

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
::::::::::::::::::::

::: test :::::::::::

> _test_not_and :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_not_and _ =
>   testName "not(and(p,q)) == or(not(p),not(q))" $
>   \p q -> eq (not (and p q)) (or (not p) (not q))
> 
> 
> _test_not_or :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> Bool)
> _test_not_or _ =
>   testName "not(or(p,q)) == and(not(p),not(q))" $
>   \p q -> eq (not (or p q)) (and (not p) (not q))

::::::::::::::::::::
::::::::::::::::::::

$\band$ and $\bor$ distribute over each other.

:::::: theorem :::::
The following hold for all $a,b,c \in \bool$.

1. $\band(a,\bor(b,c)) = \bor(\band(a,b),\band(a,c))$.
2. $\bor(a,\band(b,c)) = \band(\bor(a,b),\bor(a,c))$.

::: proof ::::::::::
1. If $a = \btrue$, we have
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
2. If $a = \btrue$, we have
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

> _test_and_or :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_and_or _ =
>   testName "and(p,or(q,r)) == or(and(p,q),and(p,r))" $
>   \p q r -> eq (and p (or q r)) (or (and p q) (and p r))
> 
> 
> _test_or_and :: (Boolean b, Equal b)
>   => b -> Test (b -> b -> b -> Bool)
> _test_or_and _ =
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
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a, TypeName a
>   , Boolean b, Arbitrary b, Show b, Equal b, TypeName b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_or p x size num = do
>   testLabel2 "or" p x
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_or_true_true p)
>   runTest args (_test_or_true_false p)
>   runTest args (_test_or_false_true p)
>   runTest args (_test_or_false_false p)
> 
>   runTest args (_test_or_true p)
>   runTest args (_test_or_false p)
>   runTest args (_test_or_not p)
>   runTest args (_test_or_idempotent p)
>   runTest args (_test_or_commutative p)
>   runTest args (_test_or_associative p)
> 
>   runTest args (_test_not_and p)
>   runTest args (_test_not_or p)
>   runTest args (_test_and_or p)
>   runTest args (_test_or_and p)
> 
>   runTest args (_test_if_or x)
>   runTest args (_test_if_or_nest x)

Main:

> main_or :: IO ()
> main_or = _test_or (true :: Bool) (true :: Bool) 20 100
