---
title: Predicates
author: nbloomf
date: 2018-01-07
tags: arithmetic-made-difficult, literate-haskell
slug: predicates
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Predicates (
>   pnot, pand, por, ptrue, pfalse, _test_predicate, main_predicate
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies

In the last post we defined the algebra of boolean values, true and false. Today we'll look at *predicates* -- functions from some set $A$ to $\bool$. It turns out the algebra on $\bool$ can be lifted to predicates, and is useful enough to collect some definitions and properties in one place.

:::::: definition ::
Let $A$ be a set. A *predicate* on $A$ is just a function $p : A \rightarrow \bool$. We define two special predicates, $\ptrue = \const(\btrue)$ and $\pfalse = \const(\bfalse)$.

In Haskell:

> ptrue :: (Boolean b) => a -> b
> ptrue _ = true
> 
> pfalse :: (Boolean b) => a -> b
> pfalse _ = false

::::::::::::::::::::

First, the basic logic operators lift.

:::::: definition ::
Let $A$ be a set. We define $\pnot : \bool^A \rightarrow \bool^A$ by $$\pnot(p)(a) = \bnot(p(a)).$$

In Haskell:

> pnot :: (Boolean b) => (a -> b) -> a -> b
> pnot p a = not (p a)

::::::::::::::::::::

$\pnot$ is an involution.

:::::: theorem :::::
Let $A$ be a set. For all $p : A \rightarrow \bool$, we have $$\pnot(\pnot(p)) = p.$$

::: proof ::::::::::
Let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \pnot(\pnot(p))(a) \\
 & = & \bnot(\pnot(p)(a)) \\
 & = & \bnot(\bnot(p(a))) \\
 & = & p(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_pnot_involutive :: (Boolean b, Equal b)
>   => a -> b -> Test ((a -> b) -> a -> Bool)
> _test_pnot_involutive _ b =
>   testName "pnot(pnot(p)) == p" $
>   \p x -> eq (pnot (pnot p) x) ((p x) `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

Special cases.

:::::: theorem :::::
Let $A$ be a set. Then we have the following.

1. $\pnot(\ptrue) = \pfalse$.
2. $\pnot(\pfalse) = \ptrue$.
3. $\bnot \circ \ptrue = \pfalse$.
4. $\bnot \circ \pfalse = \ptrue$.

::: proof ::::::::::
1. If $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pnot(\ptrue)(a) \\
 & = & \bnot(\ptrue(a)) \\
 & = & \bnot(\const(\btrue)(a)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse \\
 & = & \const(\bfalse)(a) \\
 & = & \pfalse(a)
\end{eqnarray*}$$
as needed.
2. If $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pnot(\pfalse)(a) \\
 & = & \bnot(\pfalse(a)) \\
 & = & \bnot(\const(\bfalse)(a)) \\
 & = & \bnot(\bfalse) \\
 & = & \btrue \\
 & = & \const(\btrue)(a) \\
 & = & \ptrue(a)
\end{eqnarray*}$$
as needed.
3. If $a \in A$, we have
$$\begin{eqnarray*}
 &   & (\bnot \circ \ptrue)(a) \\
 & = & \bnot(\ptrue(a)) \\
 & = & \bnot(\btrue) \\
 & = & \bfalse \\
 & = & \pfalse(a)
\end{eqnarray*}$$
as needed.
4. If $a \in A$, we have
$$\begin{eqnarray*}
 &   & (\bnot \circ \pfalse)(a) \\
 & = & \bnot(\pfalse(a)) \\
 & = & \bnot(\bfalse) \\
 & = & \btrue \\
 & = & \ptrue(a)
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_pnot_ptrue :: (Boolean b, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_pnot_ptrue _ b =
>   testName "pnot(ptrue) == pfalse" $
>   \a -> eq ((pnot ptrue) a) ((pfalse a) `withTypeOf` b)
> 
> 
> _test_pnot_pfalse :: (Boolean b, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_pnot_pfalse _ b =
>   testName "pnot(pfalse) == ptrue" $
>   \a -> eq ((pnot pfalse) a) ((ptrue a) `withTypeOf` b)
> 
> 
> _test_not_ptrue :: (Boolean b, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_not_ptrue _ b =
>   testName "(not . ptrue) == pfalse" $
>   \a -> eq ((not . ptrue) a) ((pfalse a) `withTypeOf` b)
> 
> 
> _test_not_pfalse :: (Boolean b, Equal b)
>   => a -> b -> Test (a -> Bool)
> _test_not_pfalse _ b =
>   testName "(not . pfalse) == ptrue" $
>   \a -> eq ((not . pfalse) a) ((ptrue a) `withTypeOf` b)

::::::::::::::::::::
::::::::::::::::::::

Next, $\pand$.

:::::: definition ::
Let $A$ be a set. We define $\pand : \bool^A \times \bool^A \rightarrow \bool^A$ by $$\pand(p,q)(a) = \band(p(a),q(a)).$$

In Haskell:

> pand :: (a -> Bool) -> (a -> Bool) -> a -> Bool
> pand p q a = and (p a) (q a)

::::::::::::::::::::

The usual properties of $\band$ lift to $\pand$.

:::::: theorem :::::
Let $A$ be a set. The following hold for all p,q,r \in \bool^A$.

1. $\pand(\pfalse,p) = \pand(p,\pfalse) = \pfalse$.
2. $\pand(\ptrue,p) = \pand(p,\ptrue) = p$.
3. $\pand(p,p) = p$.
4. $\pand(p,q) = \pand(q,p)$.
5. $\pand(\pand(p,q),r) = \pand(p,\pand(q,r))$.

::: proof ::::::::::
1. For all $a \in A$ we have
$$\begin{eqnarray*}
 &   & \pand(\pfalse,p)(a) \\
 & = & \band(\pfalse(a),p(a)) \\
 & = & \band(\bfalse,p(a)) \\
 & = & \bfalse \\
 & = & \pfalse(a)
\end{eqnarray*}$$
as needed; similarly for the other equality.
2. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pand(\ptrue,p)(a) \\
 & = & \band(\ptrue(a),p(a)) \\
 & = & \band(\btrue,p(a)) \\
 & = & p(a)
\end{eqnarray*}$$
as needed.
3. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pand(p,p)(a) \\
 & = & \band(p(a),p(a)) \\
 & = & p(a)
\end{eqnarray*}$$
as needed.
4. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pand(p,q)(a) \\
 & = & \band(p(a),q(a)) \\
 & = & \band(q(a),p(a)) \\
 & = & \pand(q,p)(a)
\end{eqnarray*}$$
as needed.
5. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pand(\pand(p,q),r)(a) \\
 & = & \band(\pand(p,q)(a),r(a)) \\
 & = & \band(\band(p(a),q(a)),r(a)) \\
 & = & \band(p(a),\band(q(a),r(a))) \\
 & = & \band(p(a),\pand(q,r)(a)) \\
 & = & \pand(p,\band(q,r))(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_pand_pfalse
>   :: a -> Test ((a -> Bool) -> a -> Bool)
> _test_pand_pfalse _ =
>   testName "pand(pfalse,p) == pfalse" $
>   \p a -> eq ((pand pfalse p) a) (pfalse a)
> 
> 
> _test_pand_ptrue
>   :: a -> Test ((a -> Bool) -> a -> Bool)
> _test_pand_ptrue _ =
>   testName "pand(ptrue,p) == p" $
>   \p a -> eq ((pand ptrue p) a) (p a)
> 
> 
> _test_pand_idempotent
>   :: a -> Test ((a -> Bool) -> a -> Bool)
> _test_pand_idempotent _ =
>   testName "pand(p,p) == p" $
>   \p a -> eq ((pand p p) a) (p a)
> 
> 
> _test_pand_commutative
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_pand_commutative _ =
>   testName "pand(p,q) == pand(q,p)" $
>   \p q a -> eq ((pand p q) a) ((pand q p) a)
> 
> 
> _test_pand_associative
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_pand_associative _ =
>   testName "pand(pand(p,q),r) == pand(p,pand(q,r))" $
>   \p q r a -> eq ((pand (pand p q) r) a) ((pand p (pand q r)) a)

::::::::::::::::::::
::::::::::::::::::::

Then $\por$.

:::::: definition ::
Let $A$ be a set. We define $\por : \bool^A \times \bool^A \rightarrow \bool^A$ by $$\por(p,q)(a) = \bor(p(a),q(a)).$$

In Haskell:

> por :: (a -> Bool) -> (a -> Bool) -> a -> Bool
> por p q a = or (p a) (q a)

::::::::::::::::::::

The usual properties of $\bor$ lift to $\por$.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $p,q,r \in \bool^A$.

1. $\por(\ptrue,p) = \por(p,\ptrue) = \ptrue$.
2. $\por(\pfalse,p) = \por(p,\pfalse) = p$.
3. $\por(p,p) = p$.
4. $\por(p,q) = \por(q,p)$.
5. $\por(\por(p,q),r) = \por(p,\por(q,r))$.

::: proof ::::::::::
1. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(\ptrue,p)(a) \\
 & = & \bor(\ptrue(a),p(a)) \\
 & = & \bor(\btrue,p(a)) \\
 & = & \btrue \\
 & = & \ptrue(a)
\end{eqnarray*}$$
as needed; the other equality is similar.
2. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(\pfalse,p)(a) \\
 & = & \bor(\pfalse(a),p(a)) \\
 & = & \bor(\bfalse,p(a)) \\
 & = & p(a)
\end{eqnarray*}$$
as needed; the other equality is similar.
3. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(p,p)(a) \\
 & = & \bor(p(a),p(a)) \\
 & = & p(a)
\end{eqnarray*}$$
as needed.
4. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(p,q)(a) \\
 & = & \bor(p(a),q(a)) \\
 & = & \bor(q(a),p(a)) \\
 & = & \por(q,p)(a)
\end{eqnarray*}$$
as needed.
5. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(\por(p,q),r)(a) \\
 & = & \bor(\por(p,q)(a),r(a)) \\
 & = & \bor(\bor(p(a),q(a)),r(a)) \\
 & = & \bor(p(a),\bor(q(a),r(a))) \\
 & = & \bor(p(a),\por(q,r)(a)) \\
 & = & \por(p,\por(q,r))(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_por_ptrue :: (Boolean b, Equal b)
>   => a -> b -> Test ((a -> Bool) -> a -> Bool)
> _test_por_ptrue _ b =
>   testName "por(ptrue,p) == ptrue" $
>   \p a -> eq ((por ptrue p) a) (ptrue a)
> 
> 
> _test_por_pfalse :: (Boolean b, Equal b)
>   => a -> b -> Test ((a -> Bool) -> a -> Bool)
> _test_por_pfalse _ b =
>   testName "por(pfalse,p) == p" $
>   \p a -> eq ((por pfalse p) a) (p a)
> 
> 
> _test_por_idempotent :: (Boolean b, Equal b)
>   => a -> b -> Test ((a -> Bool) -> a -> Bool)
> _test_por_idempotent _ b =
>   testName "por(p,p) == p" $
>   \p a -> eq ((por p p) a) (p a)
> 
> 
> _test_por_commutative
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_por_commutative _ =
>   testName "por(p,q) == por(q,p)" $
>   \p q a -> eq ((por p q) a) ((por q p) a)
> 
> 
> _test_por_associative
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_por_associative _ =
>   testName "por(por(p,q),r) == por(p,por(q,r))" $
>   \p q r a -> eq ((por (por p q) r) a) ((por p (por q r)) a)

::::::::::::::::::::
::::::::::::::::::::

And $\pnot$, $\pand$, and $\por$ interact.

:::::: theorem :::::
Let $A$ be a set. The following hold for all $p,q,r \in \bool^A$.

1. $\pnot(\pand(p,q)) = \por(\pnot(p),\pnot(q))$.
2. $\pnot(\por(p,q)) = \pand(\pnot(p),\pnot(q))$.
3. $\pand(p,\por(q,r)) = \por(\pand(p,q),\pand(p,r))$.
4. $\bor(p,\pand(q,r)) = \pand(\por(p,q),\por(p,r))$.

::: proof ::::::::::
1. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pnot(\pand(p,q))(a) \\
 & = & \bnot(\pand(p,q)(a)) \\
 & = & \bnot(\band(p(a),q(a))) \\
 & = & \bor(\bnot(p(a)),\bnot(q(a))) \\
 & = & \bor(\pnot(p)(a),\pnot(q)(a)) \\
 & = & \por(\pnot(p),\pnot(q))(a)
\end{eqnarray*}$$
as needed.
2. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pnot(\por(p,q))(a) \\
 & = & \bnot(\por(p,q)(a)) \\
 & = & \bnot(\bor(p(a),q(a))) \\
 & = & \band(\bnot(p(a)),\bnot(q(a))) \\
 & = & \band(\pnot(p)(a),\pnot(q)(a)) \\
 & = & \pand(\pnot(p),\pnot(q))(a)
\end{eqnarray*}$$
as needed.
3. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \pand(p,\por(q,r))(a) \\
 & = & \band(p(a),\por(q,r)(a)) \\
 & = & \band(p(a),\bor(q(a),r(a))) \\
 & = & \bor(\band(p(a),q(a)),\band(p(a),r(a))) \\
 & = & \bor(\pand(p,q)(a),\pand(p,r)(a)) \\
 & = & \por(\pand(p,q),\pand(p,r))(a)
\end{eqnarray*}$$
as needed.
4. For all $a \in A$, we have
$$\begin{eqnarray*}
 &   & \por(p,\pand(q,r))(a) \\
 & = & \bor(p(a),\pand(q,r)(a)) \\
 & = & \bor(p(a),\band(q(a),r(a))) \\
 & = & \band(\bor(p(a),q(a)),\bor(p(a),r(a))) \\
 & = & \band(\por(p,q)(a),\por(p,r)(a)) \\
 & = & \pand(\por(p,q),\por(p,r))(a)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_pnot_pand
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_pnot_pand _ =
>   testName "pnot(pand(p,q)) == por(pnot(p),pnot(q))" $
>   \p q a -> eq ((pnot (pand p q)) a) ((por (pnot p) (pnot q)) a)
> 
> 
> _test_pnot_por
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_pnot_por _ =
>   testName "pnot(por(p,q)) == pand(pnot(p),pnot(q))" $
>   \p q a -> eq ((pnot (por p q)) a) ((pand (pnot p) (pnot q)) a)
> 
> 
> _test_pand_por
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_pand_por _ =
>   testName "pand(p,por(q,r)) == por(pand(p,q),pand(p,r))" $
>   \p q r a -> eq ((pand p (por q r)) a) ((por (pand p q) (pand p r)) a)
> 
> 
> _test_por_pand
>   :: a -> Test ((a -> Bool) -> (a -> Bool) -> (a -> Bool) -> a -> Bool)
> _test_por_pand _ =
>   testName "por(p,pand(q,r)) == pand(por(p,q),por(p,r))" $
>   \p q r a -> eq ((por p (pand q r)) a) ((pand (por p q) (por p r)) a)

::::::::::::::::::::
::::::::::::::::::::

Implication lifts to predicates.

:::::: definition ::
Let $A$ be a set. We define $\pimpl : \bool^A \times \bool^A \rightarrow \bool^A$ by $\pimpl(p,q) = \btrue$ if $\pimpl(p(a),q(a)) = \btrue$ for all $a \in A$, and $\bfalse$ otherwise.
::::::::::::::::::::


Testing
-------

Suite:

> _test_predicate ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a, TypeName a
>   , TypeName b, Boolean b, Equal b, Arbitrary b
>   ) => a -> b -> Int -> Int -> IO ()
> _test_predicate x p size num = do
>   testLabel1 "predicate" x
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_pnot_involutive x p)
>   runTest args (_test_pnot_ptrue x p)
>   runTest args (_test_pnot_pfalse x p)
>   runTest args (_test_not_ptrue x p)
>   runTest args (_test_not_pfalse x p)
> 
>   runTest args (_test_pand_pfalse x)
>   runTest args (_test_pand_ptrue x)
>   runTest args (_test_pand_idempotent x)
>   runTest args (_test_pand_commutative x)
>   runTest args (_test_pand_associative x)
> 
>   runTest args (_test_por_ptrue x p)
>   runTest args (_test_por_pfalse x p)
>   runTest args (_test_por_idempotent x p)
>   runTest args (_test_por_commutative x)
>   runTest args (_test_por_associative x)
> 
>   runTest args (_test_pnot_pand x)
>   runTest args (_test_pnot_por x)
>   runTest args (_test_pand_por x)
>   runTest args (_test_por_pand x)

Main:

> main_predicate :: IO ()
> main_predicate = _test_predicate (true :: Bool) (true :: Bool) 20 100
