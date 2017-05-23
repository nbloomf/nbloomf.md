---
title: Booleans
author: nbloomf
date: 2014-04-01
tags: arithmetic-made-difficult, literate-haskell
---

> module Booleans
>   ( Bool(..), not, and, (&&&), or, (|||), ifThenElse
>   , Equal, eq, (====)
>   , runTest, testLabel, withTypeOf, TypeName(..)
>   , Show(..), String, (++), Int, IO, Maybe(..), (.), id
>   , _test_boolean, main_boolean
>   ) where
> 
> import Prelude
>   ( Show(show), IO, Bool(..), Int, Maybe(..), id
>   , putStrLn, (>>), return, (++), String, (.)
>   )
> import Test.QuickCheck
> import Test.QuickCheck.Test
> import Text.Show.Functions
> import System.Exit

Before we think about numbers or writing programs, let's start by nailing down some important functions about truth values. In math there can be a kind of other-worldness about True and False, since they live in the "metalanguage" of mathematical logic rather than the "object language" of whatever we are studying. But it will turn out to be useful to algebraify the truth values themselves.

<div class="result">
<div class="defn"><p>
We define a set $\bool = \{\btrue,\bfalse\}$. The elements of $\bool$ are called *booleans* or *truth values*.
</p></div>
</div>

We can model $\bool$ using the built in Haskell type ``Bool``, which looks something like this.

```haskell
data Bool = True | False
```

We can define the usual logical operators $\bnot$, $\band$, and $\bor$ like so:

<div class="result">
<div class="defn"><p>
We define $\bnot : \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\bnot(\btrue)  & = & \bfalse \\
\bnot(\bfalse) & = & \btrue,
\end{eqnarray*}$$
$\band : \bool \times \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\band(\btrue,\btrue)   & = & \btrue \\
\band(\btrue,\bfalse)  & = & \bfalse \\
\band(\bfalse,\btrue)  & = & \bfalse \\
\band(\bfalse,\bfalse) & = & \bfalse,
\end{eqnarray*}$$
and $\bor : \bool \times \bool \rightarrow \bool$ by
$$\begin{eqnarray*}
\bor(\btrue,\btrue)   & = & \btrue \\
\bor(\btrue,\bfalse)  & = & \btrue \\
\bor(\bfalse,\btrue)  & = & \btrue \\
\bor(\bfalse,\bfalse) & = & \bfalse.
\end{eqnarray*}$$
</p></div>
</div>

In Haskell:

> not :: Bool -> Bool
> not True  = False
> not False = True
> 
> and :: Bool -> Bool -> Bool
> and True True = True
> and _    _    = False
> 
> (&&&) = and
> 
> or :: Bool -> Bool -> Bool
> or False False = False
> or _     _     = True
> 
> (|||) = or

And $\bnot$, $\band$, and $\bor$ satisfy some nice properties.

<div class="result">
<div class="thm"><p>
The following hold for all $a,b,c \in \bool$.

1. $\bnot(\bnot(a)) = a$.
2. $\band(\bfalse,a) = \band(a,\bfalse) = \bfalse$.
3. $\band(\btrue,a) = \band(a,\btrue) = a$.
4. $\band(a,a) = a$.
5. $\band(a,b) = \band(b,a)$.
6. $\band(\band(a,b),c) = \band(a,\band(b,c))$.
7. $\bor(\btrue,a) = \bor(a,\btrue) = \btrue$.
8. $\bor(\bfalse,a) = \bor(a,\bfalse) = a$.
9. $\bor(a,a) = a$.
10. $\bor(a,b) = \bor(b,a)$.
11. $\bor(\bor(a,b),c) = \bor(a,\bor(b,c))$.
12. $\bnot(\band(a,b)) = \bor(\bnot(a),\bnot(b))$.
13. $\bnot(\bor(a,b)) = \band(\bnot(a),\bnot(b))$.
14. $\band(a,\bor(b,c)) = \bor(\band(a,b),\band(a,c))$.
15. $\bor(a,\band(b,c)) = \band(\bor(a,b),\bor(a,c))$.
</p></div>

<div class="proof"><p>
1. If $a = \btrue$ we have $$\bnot(\bnot(\btrue)) = \bnot(\bfalse) = \btrue,$$ and if $a = \bfalse$, we have $$\bnot(\bnot(\bfalse)) = \bnot(\btrue) = \bfalse$$ as claimed.
2. If $a = \btrue$ we have $$\band(\bfalse,\btrue) = \bfalse = \band(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\band(\bfalse,\bfalse) = \bfalse$$ as claimed.
3. If $a = \btrue$ we have $$\band(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\band(\btrue,\bfalse) = \bfalse = \band(\bfalse,\btrue)$$ as claimed.
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
7. If $a = \btrue$, we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ we have $$\bor(\btrue,\bfalse) = \btrue = \bor(\bfalse,\btrue)$$ as claimed.
8. If $a = \btrue$, we have $$\bor(\bfalse,\btrue) = \btrue = \bor(\btrue,\bfalse),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
9. If $a = \btrue$ we have $$\bor(\btrue,\btrue) = \btrue,$$ and if $a = \bfalse$ then $$\bor(\bfalse,\bfalse) = \bfalse$$ as claimed.
10. If $a = \btrue$ we have $$\bor(\btrue,b) = \btrue = \bor(b,\btrue),$$ and if $a = \bfalse$ we have $$\bor(\bfalse,b) = b = \bor(b,\bfalse)$$ as claimed.
11. If $a = \btrue$ we have
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
12. If $a = \btrue$, we have
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
13. If $a = \btrue$, we have
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
14. If $a = \btrue$, we have
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
15. If $a = \btrue$, we have
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
</div>

Wow, that was tedious! But we only have to do it once. :)

Next we nail down conditional expressions.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. We define a map $\bif : \bool \times A \times A \rightarrow A$ by
$$\begin{eqnarray*}
\bif(\btrue,u,v)  & = & u \\
\bif(\bfalse,u,v) & = & v.
\end{eqnarray*}$$
</p></div>
</div>

In Haskell:

> ifThenElse :: Bool -> a -> a -> a
> ifThenElse True  x _ = x
> ifThenElse False _ x = x

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $p \in \bool$ and $u,v \in A$, we have $$f(\bif(p,u,v)) = \bif(p,f(u),f(v)).$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif(p,u,v)) \\
 & = & f(\bif(\btrue,u,v)) \\
 & = & f(u) \\
 & = & \bif(\btrue,f(u),f(v)) \\
 & = & \bif(p,f(u),f(v))
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & f(\bif(p,u,v)) \\
 & = & f(\bif(\bfalse,u,v)) \\
 & = & f(v) \\
 & = & \bif(\bfalse,f(u),f(v)) \\
 & = & \bif(p,f(u),f(v))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Nested $\bif{\ast}{\ast}{\ast}$s commute (sort of).

<div class="result">
<div class="thm"><p>
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
</div>


Equality
--------

Now that we've algebraified truth values, we will also algebraify equality. Typically I think of equality (as in the $=$ symbol) as a metalanguage expression. Sure, we can define a relation that captures equality on a given set, but really equality is a "logical" thing, not a "mathematical" one. We'll express this using a type class in Haskell like so.

> class Equal a where
>   eq :: a -> a -> Bool
> 
> -- alias
> (====) :: (Equal a) => a -> a -> Bool
> (====) = eq
> 
> infixr 0 ====

(Why not use the built in `Eq` class? No good reason.) For example, here is the ``Equal`` instance for ``Bool``:

> instance Equal Bool where
>   eq True  True  = True
>   eq True  False = False
>   eq False True  = False
>   eq False False = True
> 
> instance Equal a => Equal (Maybe a) where
>   eq Nothing  Nothing  = True
>   eq Nothing  (Just _) = False
>   eq (Just _) Nothing  = False
>   eq (Just x) (Just y) = eq x y
> 
> instance (Equal a, Equal b) => Equal (a,b) where
>   eq (a1,b1) (a2,b2) = (a1 ==== a2) &&& (b1 ==== b2)


Testing
-------

Here are our property tests for $\bnot$:

> -- not(not(p)) == p
> _test_not_involutive :: Bool -> Bool
> _test_not_involutive p =
>   (not (not p)) ==== p

Tests for $\band$:

> -- and(false,p) == false
> _test_and_false :: Bool -> Bool
> _test_and_false p =
>   (and False p) ==== False
> 
> 
> -- and(true,p) == p
> _test_and_true :: Bool -> Bool
> _test_and_true p =
>   (and True p) ==== p
> 
> 
> -- and(p,p) == p
> _test_and_idempotent :: Bool -> Bool
> _test_and_idempotent p =
>   (and p p) ==== p
> 
> 
> -- and(p,q) == and(q,p)
> _test_and_commutative :: Bool -> Bool -> Bool
> _test_and_commutative p q =
>   (and p q) ==== (and q p)
> 
> 
> -- and(and(p,q),r) == and(p,and(q,r))
> _test_and_associative :: Bool -> Bool -> Bool -> Bool
> _test_and_associative p q r =
>   (and (and p q) r) ==== (and p (and q r))

Tests for $\bor$:

> -- or(true,p) == true
> _test_or_true :: Bool -> Bool
> _test_or_true p =
>   (or True p) ==== True
> 
> 
> -- or(false,p) == p
> _test_or_false :: Bool -> Bool
> _test_or_false p =
>   (or False p) ==== p
> 
> 
> -- or(p,p) == p
> _test_or_idempotent :: Bool -> Bool
> _test_or_idempotent p =
>   (or p p) ==== p
> 
> 
> -- or(p,q) == or(q,p)
> _test_or_commutative :: Bool -> Bool -> Bool
> _test_or_commutative p q =
>   (or p q) ==== (or q p)
> 
> 
> -- or(or(p,q),r) == or(p,or(q,r))
> _test_or_associative :: Bool -> Bool -> Bool -> Bool
> _test_or_associative p q r =
>   (or (or p q) r) ==== (or p (or q r))

Tests for more than one function:

> -- not(and(p,q)) == or(not(p),not(q))
> _test_not_and :: Bool -> Bool -> Bool
> _test_not_and p q =
>   (not (and p q)) ==== (or (not p) (not q))
> 
> 
> -- not(or(p,q)) == and(not(p),not(q))
> _test_not_or :: Bool -> Bool -> Bool
> _test_not_or p q =
>   (not (or p q)) ==== (and (not p) (not q))
> 
> 
> -- and(p,or(q,r)) == or(and(p,q),and(p,r))
> _test_and_or :: Bool -> Bool -> Bool -> Bool
> _test_and_or p q r =
>   (and p (or q r)) ==== (or (and p q) (and p r))
> 
> 
> -- or(p,and(q,r)) == and(or(p,q),or(p,r))
> _test_or_and :: Bool -> Bool -> Bool -> Bool
> _test_or_and p q r =
>   (or p (and q r)) ==== (and (or p q) (or p r))

One of our main uses for ``Bool`` will be checking the results of tests, so this is as good a place as any to introduce a couple of QuickCheck helper functions for this.

> runTest :: Testable prop => Args -> prop -> IO ()
> runTest args prop = do
>   result <- quickCheckWithResult args prop
>   if isSuccess result
>     then return ()
>     else putStrLn (show result) >> exitFailure
> 
> testLabel :: String -> IO ()
> testLabel msg = putStrLn ("\x1b[1;32m" ++ msg ++ "\x1b[0;39;49m")
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

> -- run all tests for booleans
> _test_boolean :: Int -> Int -> IO ()
> _test_boolean size num = do
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
>   runTest args _test_and_idempotent
>   runTest args _test_and_commutative
>   runTest args _test_and_associative
> 
>   runTest args _test_or_true
>   runTest args _test_or_false
>   runTest args _test_or_idempotent
>   runTest args _test_or_commutative
>   runTest args _test_or_associative
> 
>   runTest args _test_not_and
>   runTest args _test_not_or
>   runTest args _test_and_or
>   runTest args _test_or_and

And ``main``:

> main_boolean :: IO ()
> main_boolean = _test_boolean 20 100
