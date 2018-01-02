---
title: TakeWhile and DropWhile
author: nbloomf
date: 2017-12-16
tags: arithmetic-made-difficult, literate-haskell
slug: takewhile-dropwhile
---

> module TakeWhileAndDropWhile
>   ( takeWhile, dropWhile
>   , _test_takewhile_dropwhile, main_takewhile_dropwhile
>   ) where
> 
> import Booleans
> import Tuples
> import DisjointUnions
> import NaturalNumbers
> import Plus
> import MaxAndMin
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import UnfoldN
> import Zip
> import Prefix
> import AllAndAny
> import TailsAndInits
> import Filter
> import Elt
> import Count
> import Repeat
> import Select
> import Unique
> import Delete
> import Dedupe
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll define two functions, $\takeWhile$ and $\dropWhile$, similar to $\take$ and $\drop$, but instead of taking or dropping a prefix of some length, we will take or drop the longest prefix satisfying some predicate. We'd like $\takeBut$ to have a signature like $$\takeWhile : \bool^A \times \lists{A} \rightarrow \lists{A}.$$

As usual, suppose $\takeWhile$ can be defined in terms of fold; say $$\takeWhile(p,x) = \foldr{e}{\varphi}(x)$$ for some $e$ and $\varphi$. To make the types work out we need $e \in \lists{A}$ and $\varphi : A \times \lists{A} \rightarrow \lists{A}$. Thinking about the desired behavior for $\takeWhile$, we need

$$\begin{eqnarray*}
 &   & \nil \\
 & = & \takeWhile(p,\nil) \\
 & = & \foldr{e}{\varphi}(\nil) \\
 & = & e
\end{eqnarray*}$$

and

$$\begin{eqnarray*}
 &   & \bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil} \\
 & = & \takeWhile(p,\cons(a,x)) \\
 & = & \foldr{e}{\varphi}(\cons(a,x)) \\
 & = & \varphi(a,\foldr{e}{\varphi}(x)) \\
 & = & \varphi(a,\takeWhile(p,x))
\end{eqnarray*}$$

With this in mind, we define $\takeWhile$ like so.

<div class="result">
<div class="defn"><p>
Let $A$ be a set, with $p : A \rightarrow \bool$. Define $\varphi(p) : A \times \lists{A} \rightarrow \lists{A}$ by $$\varphi(p)(a,x) = \left\{ \begin{array}{ll} \cons(a,x) & \mathrm{if}\ p(a) = \btrue \\ \nil & \mathrm{otherwise}. \end{array} \right.$$

We define $\takeWhile : \bool^A \times \lists{A} \rightarrow \lists{A}$ by $$\takeWhile(p,x) = \foldr{\nil}{\varphi(p)}(x).$$

In Haskell:

> takeWhile' :: (List t) => (a -> Bool) -> t a -> t a
> takeWhile' p = foldr nil phi
>   where
>     phi a x = if eq (p a) True
>       then cons a x
>       else nil

</p></div>
</div>

As usual, since $\takeWhile$ is defined directly in terms of foldr it is the unique solution to a system of functional equations.

<div class="result">
<div class="thm">
Let $A$ be a set. Then $\takeWhile$ is the unique function $$f : \bool^A \times \lists{A} \rightarrow \lists{A}$$ having the property that $$\left\{ \begin{array}{l} f(p,\nil) = \nil \\ f(p,\cons(a,x)) = \bif{p(a)}{\cons(a,f(p,x)}{\nil}. \end{array} \right.$$
</div>

<div class="proof">
That $\takeWhile$ is a solution to this system falls out of the definition. Note that
$$\begin{eqnarray*}
 &   & \takeWhile(p,\nil) \\
 & = & \foldr{\nil}{\varphi(p)}(\nil) \\
 & = & \nil
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \takeWhile(p,\cons(a,x)) \\
 & = & \foldr{\nil}{\varphi(p)}(\cons(a,x)) \\
 & = & \varphi(p)(a,\foldr{\nil}{\varphi(p)}(x)) \\
 & = & \varphi(p)(a,\takeWhile(p,x)) \\
 & = & \bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil}
\end{eqnarray*}$$
as claimed.

To see uniqueness, note that under these conditions we have $$f(p,x) = \foldr{\nil}{\varphi(p)}(x) = \takeWhile(p,x)$$ as claimed.
</div>
</div>

In Haskell:

> takeWhile :: (List t) => (a -> Bool) -> t a -> t a
> takeWhile p z = case unnext z of
>   Left ()     -> nil
>   Right (a,x) -> if eq (p a) True
>     then cons a (takeWhile p x)
>     else nil

Now $\takeWhile$ is a prefix:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and $p : A \rightarrow \bool$. For all $x \in \lists{A}$, we have $$\prefix(\takeWhile(p,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\takeWhile(p,\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. We have
$$\begin{eqnarray*}
 &   & \prefix(\takeWhile(p,\cons(a,x),\cons(a,x))) \\
 & = & \prefix(\bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil},\cons(a,x)) \\
 & = & \bif{p(a)}{\prefix(\cons(a,\takeWhile(p,x)),\cons(a,x))}{\prefix(\nil,\cons(a,x))} \\
 & = & \bif{p(a)}{\prefix(\takeWhile(p,x),x)}{\btrue} \\
 & = & \bif{p(a)}{\btrue}{\btrue} \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

So $\takeWhile$ is a sublist:

<div class="result">
<div class="corollary"><p>
Let $A$ be a set, with $p : A \rightarrow \bool$ and $x \in \lists{A}$. Then we have $$\sublist(\takeWhile(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have $$\prefix(\takeWhile(k,x),x) = \btrue,$$ so $$\infix(\takeWhile(k,x),x) = \btrue,$$ so $$\sublist(\takeWhile(k,x),x) = \btrue$$ as claimed.
</p></div>
</div>

$\takeWhile$ is idempotent:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $p : A \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\takeWhile(p,\takeWhile(p,x)) = \takeWhile(p,x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,x)) \\
 & = & \takeWhile(p,\takeWhile(p,\nil)) \\
 & = & \takeWhile(p,\nil) \\
 & = & \takeWhile(p,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,\cons(a,x))) \\
 & = & \takeWhile(p,\cons(a,\takeWhile(p,x))) \\
 & = & \cons(a,\takeWhile(p,\takeWhile(p,x))) \\
 & = & \cons(a,\takeWhile(p,x)) \\
 & = & \takeWhile(p,\cons(a,x))
\end{eqnarray*}$$
as needed. If $p(a) = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(p,\cons(a,x))) \\
 & = & \takeWhile(p,\nil) \\
 & = & \nil \\
 & = & \takeWhile(p,\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\takeWhile$ commutes with itself (kind of):

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $p$ and $q$ mappings $A \rightarrow \bool$. Then for all $x \in \lists{A}$ we have $$\takeWhile(p,\takeWhile(q,x)) = \takeWhile(q,\takeWhile(p,x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(q,x)) \\
 & = & \takeWhile(p,\takeWhile(q,\nil)) \\
 & = & \takeWhile(p,\nil) \\
 & = & \nil \\
 & = & \takeWhile(q,\nil) \\
 & = & \takeWhile(q,\takeWhile(p,\nil)) \\
 & = & \takeWhile(q,\takeWhile(p,x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x \in \lists{A}$, and let $a \in A$. If $p(a) = \btrue$, we have
$$\begin{eqnarray*}
 &   & \takeWhile(p,\takeWhile(q,\cons(a,x))) \\
 & = & \takeWhile(p,\bif{q(a)}{\cons(a,\takeWhile(q,x))}{\nil}) \\
 & = & \bif{q(a)}{\takeWhile(p,\cons(a,\takeWhile(q,x)))}{\takeWhile(p,\nil)} \\
 & = & \bif{q(a)}{\bif{p(a)}{\cons(a,\takeWhile(p,\takeWhile(q,x)))}{\nil}}{\nil} \\
 & = & \bif{q(a)}{\bif{p(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\bif{p(a)}{\nil}{\nil}} \\
 & = & \bif{p(a)}{\bif{q(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\bif{q(a)}{\nil}{\nil}} \\
 & = & \bif{p(a)}{\bif{q(a)}{\cons(a,\takeWhile(q,\takeWhile(p,x)))}{\nil}}{\nil} \\
 & = & \bif{p(a)}{\takeWhile(q,\cons(a,\takeWhile(p,x)))}{\takeWhile(q,\nil)} \\
 & = & \takeWhile(q,\bif{p(a)}{\cons(a,\takeWhile(p,x))}{\nil}) \\
 & = & \takeWhile(q,\takeWhile(p,\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now for $\dropWhile$. This function should drop the longest prefix satisfying some predicate, again with signature $\bool^A \times \lists{A} \rightarrow \lists{A}$. If we try defining this using foldr in the "obvious" way, we run into trouble, where the $\varphi$ parameter needs to have its argument and eat it too. (try it!) One way around this is the trick we used to define $\zip$.

Suppose $$\dropWhile(p,x) = \foldr{e}{\varphi}(x)(x)$$ for some $e$ and $\varphi$. To make the types work out, we need $$e \in \lists{A}^{\lists{A}}$$ and $$\varphi : A \times \lists{A}^{\lists{A}} \rightarrow \lists{A}^{\lists{A}};$$ now
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \dropWhile(p,\nil) \\
 & = & \foldr{e}{\varphi}(\nil)(\nil) \\
 & = & e(\nil)
\end{eqnarray*}$$
and
$$\begin{eqnarray*}
 &   & \varphi(a,\foldr{e}{\varphi}(x))(\cons(a,x)) \\
 & = & \foldr{e}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \dropWhile(p,\cons(a,x)) \\
 & = & \bif{p(a)}{\dropWhile(p,x)}{\cons(a,x)}
\end{eqnarray*}$$

(that last line is why using a plain fold doesn't work.) With this in mind, we define $\dropWhile$ like so.

<div class="result">
<div class="dfn">
Let $A$ be a set with $p : A \rightarrow \bool$. Define $\varphi(p) : A \times \lists{A}^{\lists{A}} \rightarrow \lists{A}^{\lists{A}}$ by $$\varphi(p)(a,f)(x) = \bif{p(a)}{f(\tail(x))}{x}.$$ Now define $$\dropWhile : \bool^A \times \lists{A} \rightarrow \lists{A}$$ by $$\dropWhile(p,x) = \foldr{\id}{\varphi(p)}(x)(x).$$

In Haskell:

> dropWhile', dropWhile :: (List t) => (a -> Bool) -> t a -> t a
> dropWhile' p x = foldr id phi x x
>   where
>     phi a f x = if eq (p a) True
>       then f (tail x)
>       else x
> 
> dropWhile = dropWhile'

</div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have the following.

1. $\dropBut(\zero,x) = \nil$.
2. $\dropBut(k,\nil) = \nil$.
3. $\dropBut(\next(k),\snoc(a,x)) = \snoc(a,\dropBut(k,x))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \dropBut(\zero,x) \\
 & = & \rev(\take(\zero,\rev(x))) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. We have
$$\begin{eqnarray*}
 &   & \dropBut(k,\nil) \\
 & = & \rev(\take(k,\rev(\nil))) \\
 & = & \rev(\take(k,\nil)) \\
 & = & \rev(\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \dropBut(\next(k),\snoc(a,x)) \\
 & = & \rev(\take(\next(k),\rev(\snoc(a,x)))) \\
 & = & \rev(\take(\next(k),\cons(a,\rev(x)))) \\
 & = & \rev(\cons(a,\take(k,\rev(x)))) \\
 & = & \snoc(a,\rev(\take(k,\rev(x)))) \\
 & = & \snoc(a,\dropBut(k,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Now $\dropBut$ is a $\suffix$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\suffix(\dropBut(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \suffix(\dropBut(k,x),x) \\
 & = & \suffix(\rev(\take(k,\rev(x))),x) \\
 & = & \suffix(\rev(\take(k,\rev(x))),\rev(\rev(x))) \\
 & = & \prefix(\take(k,\rev(x)),\rev(x)) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Finally, $\takeBut$ and $\dropBut$ give a kind of $\cat$-factorization.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$x = \cat(\takeBut(k,x),\dropBut(k,x)).$$
</p></div>

<div class="proof"><p>
We have
$$\begin{eqnarray*}
 &   & \cat(\takeBut(k,x),\dropBut(k,x)) \\
 & = & \cat(\rev(\drop(k,\rev(x))),\rev(\take(k,\rev(x)))) \\
 & = & \rev(\cat(\take(k,\rev(x)),\drop(k,\rev(x)))) \\
 & = & \rev(\rev(x)) \\
 & = & x
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\takeWhile$:

> _test_takeWhile_alt :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_alt _ =
>   testName "takeWhile(p,x) == takeWhile'(p,x)" $
>   \p x -> eq (takeWhile p x) (takeWhile' p x)
> 
> 
> _test_takeWhile_prefix :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_prefix _ =
>   testName "prefix(takeWhile(p,x),x) == true" $
>   \p x -> eq (prefix (takeWhile p x) x) True
> 
> 
> _test_takeWhile_idempotent :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> t a -> Bool)
> _test_takeWhile_idempotent _ =
>   testName "takeWhile(p,takeWhile(p,x)) == takeWhile(p,x)" $
>   \p x -> eq (takeWhile p (takeWhile p x)) (takeWhile p x)
> 
> 
> _test_takeWhile_commutes :: (List t, Equal a)
>   => t a -> Test ((a -> Bool) -> (a -> Bool) -> t a -> Bool)
> _test_takeWhile_commutes _ =
>   testName "takeWhile(p,takeWhile(q,x)) == takeWhile(q,takeWhile(p,x))" $
>   \p q x ->
>     eq (takeWhile p (takeWhile q x)) (takeWhile q (takeWhile p x))

And for $\dropBut$:

 > _test_dropWhile_suffix :: (List t, Equal a, Natural n)
 >   => t a -> n -> Test (n -> t a -> Bool)
 > _test_dropWhile_suffix _ _ =
 >   testName "suffix(dropBut(k,x),x) == true" $
 >   \k x -> eq (suffix (dropBut k x) x) True

And for both:

 > _test_takeWhile_dropWhile_cat :: (List t, Equal a, Natural n)
 >   => t a -> n -> Test (n -> t a -> Bool)
 > _test_takeWhile_dropWhile_cat _ _ =
 >   testName "cat(takeBut(k,x),dropBut(k,x)) == x" $
 >   \k x -> eq (cat (takeBut k x) (dropBut k x)) x

And the suite:

> -- run all tests for takeBut & dropBut
> _test_takewhile_dropwhile ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_takewhile_dropwhile t k maxSize numCases = do
>   testLabel ("takeWhile & dropWhile: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_takeWhile_alt t)
>   runTest args (_test_takeWhile_prefix t)
>   runTest args (_test_takeWhile_idempotent t)
>   runTest args (_test_takeWhile_commutes t)
> 
>   --runTest args (_test_dropWhile_suffix t)
> 
>   --runTest args (_test_takeWhile_dropWhile_cat t)

And ``main``:

> main_takewhile_dropwhile :: IO ()
> main_takewhile_dropwhile = do
>   _test_takewhile_dropwhile (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_takewhile_dropwhile (nil :: ConsList Unary) (zero :: Unary) 20 100
