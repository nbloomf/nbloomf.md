---
title: Count
author: nbloomf
date: 2017-05-21
tags: arithmetic-made-difficult, literate-haskell
---

> module Count
>   ( count, _test_count, main_count
>   ) where
> 
> import Booleans
> import NaturalNumbers
> import Plus
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define $\count$, which takes an $A$ and a $\lists{A}$ and returns the number of items in the $\lists{A}$ that are identical to the $A$. As usual we'll define this as a fold. Note that -- unlike some of the other list functions  we've seen -- in principle, $\count$ shouldn't care so much what *order* the items in its input come in. Moreover, note that $\count$ necessarily must examine every item in its input if it's going to return the correct answer. When this happens -- we don't care about order but have to look at every item -- the *left fold* operator can be used instead of the right fold, with the advantage that left fold is more space efficient.

With this in mind, we define $\count$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, and define $\varphi : A \rightarrow A \times \nats \rightarrow \nats$ by $$\varphi(a)(b,k) = \bif{\beq(a,b)}{\next(k)}{k}.$$ Then define $\count : A \times \lists{A} \rightarrow \nats$ by $$\count(a,x) = \foldl{\zero}{\varphi(a)}(x).$$
</p></div>
</div>

In Haskell:

> count :: (List t, Equal a, Natural n) => a -> t a -> n
> count a x = foldl zero (phi a) x
>   where
>     phi u b k = ifThenElse (eq u b) (next k) k

Recall that $\foldl{e}{\varphi} = \foldr{e}{\varphi}$ if $\varphi$ has the property that $$\varphi(a,\varphi(b,e)) = \varphi(b,\varphi(a,e))$$ for all $a$, $b$, and $e$. I claim that the function $\varphi(a)$ in the definition of $\count$ has this property.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, and let $\varphi$ be as in the definition of $\count$. Then for all $a,b,c \in A$ and $k \in \nats$, we have $$\varphi(a)(b,\varphi(a)(c,k)) = \varphi(a)(c,\varphi(a)(b,k)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \varphi(a)(b,\varphi(a)(c,k)) \\
 & = & \varphi(a)(b,\bif{\beq(a,c)}{\next(k)}{k}) \\
 & = & \bif{\beq(a,b)}{\next(\bif{\beq(a,c)}{\next(k)}{k})}{\bif{\beq(a,c)}{\next(k)}{k}} \\
 & = & \bif{\beq(a,b)}{\bif{\beq(a,c)}{\next(\next(k))}{\next(k)}}{\bif{\beq(a,c)}{\next(k)}{k}} \\
 & = & \bif{\beq(a,c)}{\bif{\beq(a,b)}{\next(\next(k))}{\next(k)}}{\bif{\beq(a,b)}{\next(k)}{k}} \\
 & = & \bif{\beq(a,c)}{\next(\bif{\beq(a,b)}{\next(k)}{k})}{\bif{\beq(a,b)}{\next(k)}{k}} \\
 & = & \varphi(a)(c,\bif{\beq(a,b)}{\next(k)}{k}) \\
 & = & \varphi(a)(c,\varphi(a)(b,k))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

So we can evaluate $\count$ as a left fold, but reason about $\count$ as a right fold.

Special cases.

<div class="result">
<div class="thm"><p>
Let $A$ be a set.

1. $\count(a,\nil) = \zero$.
2. $\count(a,\cons(b,\nil)) = \bif{\beq(a,b)}{\next(\zero)}{\zero}$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \count(a,\nil) \\
 & = & \foldl{\zero}{\varphi(a)}(\nil) \\
 & = & \zero
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,\nil)) \\
 & = & \foldl{\zero}{\varphi(a)}(\cons(b,\nil)) \\
 & = & \foldl{\varphi(a)(b,\zero)}{\varphi(a)}(\nil) \\
 & = & \varphi(a)(b,\zero) \\
 & = & \bif{\beq(a,b)}{\next(\zero)}{\zero}
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\count$ respects $\rev$ and $\cat$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$ and $x,y \in \lists{A}$ we have the following.

1. $\count(a,\snoc(b,x)) = \count(a,\cons(b,x))$.
2. $\count(a,\rev(x)) = \count(a,x)$.
3. $\count(a,\cons(b,x)) = \bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)}$.
4. $\count(a,\cat(x,y)) = \nplus(\count(a,x),\count(a,y))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \count(a,\snoc(b,x)) \\
 & = & \foldr{\zero}{\varphi(a)}(\snoc(b,x)) \\
 & = & \foldr{\zero}{\varphi(a)}(\cons(b,x)) \\
 & = & \count(a,\cons(b,x))
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \count(a,\rev(x)) \\
 & = & \foldr{\zero}{\varphi(a)}(\rev(x)) \\
 & = & \foldr{\zero}{\varphi(a)}(x) \\
 & = & \count(a,x)
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \foldr{\zero}{\varphi(a)}(\cons(b,x)) \\
 & = & \varphi(a)(b,\foldr{\zero}{\varphi(a)}(x)) \\
 & = & \varphi(a)(b,\count(a,x)) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)}
\end{eqnarray*}$$
as claimed.
4. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(x,y)) \\
 & = & \count(a,\cat(\nil,y)) \\
 & = & \count(a,y) \\
 & = & \nplus(\zero,\count(a,y)) \\
 & = & \nplus(\count(a,\nil),\count(a,y)) \\
 & = & \nplus(\count(a,x),\count(a,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $y$ and $a$ for some $x$, and let $b \in A$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(\cons(b,x),y)) \\
 & = & \count(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,\cat(x,y)))}{\count(a,\cat(x,y))} \\
 & = & \next(\count(a,\cat(x,y))) \\
 & = & \next(\nplus(\count(a,x),\count(a,y))) \\
 & = & \nplus(\next(\count(a,x)),\count(a,y)) \\
 & = & \nplus(\bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)},\count(a,y)) \\
 & = & \nplus(\count(a,\cons(b,x)),\count(a,y))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cat(\cons(b,x),y)) \\
 & = & \count(a,\cons(b,\cat(x,y))) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,\cat(x,y)))}{\count(a,\cat(x,y))} \\
 & = & \count(a,\cat(x,y)) \\
 & = & \nplus(\count(a,x),\count(a,y)) \\
 & = & \nplus(\bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)},\count(a,y)) \\
 & = & \nplus(\count(a,\cons(b,x)),\count(a,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\count$ is a $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. We have $$\count(a,x) = \length(\filter(\beq(a,-),x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,x) \\
 & = & \count(a,\nil) \\
 & = & \foldr{\zero}{\varphi(a)}(\nil) \\
 & = & \zero \\
 & = & \length(\nil) \\
 & = & \length(\filter(\beq(a,-),\nil)) \\
 & = & \length(\filter(\beq(a,-),x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $b \in A$. We consider two possibilities. If $a = b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,\cons(a,x)) \\
 & = & \bif{\beq(a,a)}{\next(\count(a,x))}{\count(a,x)} \\
 & = & \next(\count(a,x)) \\
 & = & \next(\length(\filter(\beq(a,-),x))) \\
 & = & \length(\cons(a,\filter(\beq(a,-),x))) \\
 & = & \length(\filter(\beq(a,-),\cons(a,x)))
\end{eqnarray*}$$
as needed. If $a \neq b$, we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \bif{\beq(a,b)}{\next(\count(a,x))}{\count(a,x)} \\
 & = & \count(a,x) \\
 & = & \length(\filter(\beq(a,-),x)) \\
 & = & \length(\filter(\beq(a,-),\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\count$ interacts with $\map(f)$ if $f$ is injective.

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets and $f : A \rightarrow B$ an injective map. Then $$\count(a,x) = \count(f(a),\map(f)(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \count(a,x) \\
 & = & \count(a,\nil) \\
 & = & \count(a,\map(f)(\nil)) \\
 & = & \count(a,\map(f)(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$, and let $b \in A$. We consider two possibilities. If $a = b$, then $f(a) = f(b)$, and we have
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,\cons(a,x)) \\
 & = & \next(\count(a,x)) \\
 & = & \next(\count(f(a),\map(f)(x))) \\
 & = & \count(f(a),\cons(f(a),\map(f)(x))) \\
 & = & \count(f(a),\map(f)(\cons(a,x))) \\
 & = & \count(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed. If $a \neq b$, then we have $f(a) \neq f(b)$ (since $f$ is injective), so that
$$\begin{eqnarray*}
 &   & \count(a,\cons(b,x)) \\
 & = & \count(a,x) \\
 & = & \count(f(a),\map(f)(x)) \\
 & = & \count(f(a),\cons(f(b),\map(f)(x))) \\
 & = & \count(f(a),\map(f)(\cons(b,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\count$:

> -- count(a,nil) == zero
> _test_count_nil :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> Bool
> _test_count_nil t k a =
>  let
>    nil'  = nil `withTypeOf` ListOf t
>    zero' = zero `withTypeOf` Nat k
>  in
>    (count a nil') ==== zero'
> 
> 
> -- count(a,cons(a,nil)) == next(zero)
> _test_count_one :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> Bool
> _test_count_one t k a =
>  let
>    nil' = nil `withTypeOf` ListOf t
>    one  = next zero `withTypeOf` Nat k
>  in
>    (count a (cons a nil')) ==== one
> 
> 
> -- count(a,cons(a,nil)) == next(zero)
> _test_count_rev :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> ListOf t a -> Bool
> _test_count_rev t k a x =
>  let
>    cx = count a x `withTypeOf` Nat k
>  in
>    (count a (rev x)) ==== cx
> 
> 
> -- count(a,cons(a,nil)) == next(zero)
> _test_count_snoc_cons :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> a -> ListOf t a -> Bool
> _test_count_snoc_cons t k a b x =
>  let
>    cbx = count a (cons b x) `withTypeOf` Nat k
>  in
>    (count a (snoc b x)) ==== cbx
> 
> 
> -- count(a,cat(x,y)) == plus(count(a,x),count(a,y))
> _test_count_cat :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> ListOf t a -> ListOf t a -> Bool
> _test_count_cat t k a x y =
>  let
>    cx = count a x `withTypeOf` Nat k
>  in
>    (count a (cat x y)) ==== plus cx (count a y)
> 
> 
> -- count(a,x) == length(filter(eq(a,-),x))
> _test_count_length :: (List t, Equal a, Natural n)
>   => t a -> n -> a -> ListOf t a -> Bool
> _test_count_length t k a x =
>  let
>    cx = count a x `withTypeOf` Nat k
>  in
>    cx ==== (length (filter (eq a) x))

And the suite:

> -- run all tests for count
> _test_count ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a
>   , List t
>   , Natural n
>   ) => String -> t a -> n -> Int -> Int -> IO ()
> _test_count label t n maxSize numCases = do
>   testLabel ("count: " ++ label)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_count_nil t n)
>   runTest args (_test_count_one t n)
>   runTest args (_test_count_snoc_cons t n)
>   runTest args (_test_count_rev t n)
>   runTest args (_test_count_cat t n)
>   runTest args (_test_count_length t n)

And ``main``:

> main_count :: IO ()
> main_count = do
>   _test_count "ConsList Bool; Unary"  (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_count "ConsList Unary; Unary" (nil :: ConsList Unary) (zero :: Unary) 20 100
