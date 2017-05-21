---
title: Tails and Inits
author: nbloomf
date: 2017-05-12
tags: arithmetic-made-difficult, literate-haskell
---

> {-# LANGUAGE FlexibleInstances #-}
> module TailsAndInits
>   ( tails, inits, _test_tails_inits, main_tails_inits
>   ) where
> 
> import Booleans
> import NaturalNumbers
> 
> import Lists
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import Prefix
> import LongestCommonPrefix
> import AllAndAny
> 
> import Prelude ()
> import Test.QuickCheck
> import Text.Show.Functions

Today we'll construct the lists of all suffixes ($\tails$) and prefixes ($\inits$) of a list. Starting with $\tails$: this function should have a signature like $$\lists{A} \rightarrow \lists{\lists{A}}.$$ Here's how I did it: we have (almost) one suffix for each item in the list -- the suffix starting at that item -- plus the empty suffix. This suggests we can define $\tails$ as a fold. The hitch is in the return type; fold prefers to decompose a list, while it appears that $\tails$ is building a list up. As usual, the way to handle this is by folding a list of *functions*. The only way I can see to do this is by defining $\tails$ as $$\tails(x) = \foldr{\varepsilon}{\varphi}(x)(x)$$ for some appropriate $\varepsilon$ and $\varphi$. Unpacking this using the behavior we want, I get the following definition.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\varepsilon(w) = \cons(w,\nil)$$ and define $\varphi : A \times \lists{\lists{A}}^{\lists{A}} \rightarrow \lists{\lists{A}}^{\lists{A}}$ by $$\varphi(a,f)(w) = \cons(w,f(\tail(w))).$$ Now define $\tails : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\tails(x) = \foldr{\varepsilon}{\varphi}(x)(x).$$
</p></div>
</div>

We can translate $\tails$ to Haskell directly as follows:

> tails' :: (List t) => t a -> t (t a)
> tails' x = foldr epsilon phi x x
>   where
>     epsilon w = cons w nil
>     phi _ f w = cons w (f (tail w))

The next result suggests a more straightforward implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$ we have the following.

1. $\tails(\nil) = \cons(\nil,\nil)$.
2. $\tails(\cons(a,x)) = \cons(\cons(a,x),\tails(x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \tails(\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(\nil) \\
 & = & \varepsilon(\nil) \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \tails(\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\cons(a,x)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\cons(a,x)) \\
 & = & \cons(\cons(a,x),\foldr{\varepsilon}{\varphi}(x)(\tail(\cons(a,x)))) \\
 & = & \cons(\cons(a,x),\foldr{\varepsilon}{\varphi}(x)(x)) \\
 & = & \cons(\cons(a,x),\tails(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> tails :: (List t) => t a -> t (t a)
> tails x = case listShape x of
>   Nil      -> cons nil nil
>   Cons a w -> cons (cons a w) (tails w)

Special case.

<div class="result">
<div class="thm"><p>
Let $A$ be a sets. For all $a \in A$ we have $$\tails(\cons(a,\nil)) = \cons(\cons(a,\nil),\cons(\nil,\nil)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \tails(\cons(a,\nil)) \\
 & = & \cons(\cons(a,\nil),\tails(\nil)) \\
 & = & \cons(\cons(a,\nil),\cons(\nil,\nil))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\tails$ interacts with $\map$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$ we have $$\tails(\map(f)(x)) = \map(\map(f))(\tails(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\nil)) \\
 & = & \tails(\nil) \\
 & = & \nil \\
 & = & \map(\map(f))(\nil) \\
 & = & \map(\map(f))(\tails(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \tails(\map(f)(\cons(a,x))) \\
 & = & \tails(\cons(f(a),\map(f)(x))) \\
 & = & \cons(\cons(f(a),\map(f)(x)),\tails(\map(f)(x))) \\
 & = & \cons(\cons(f(a),\map(f)(x)),\map(\map(f))(\tails(x))) \\
 & = & \cons(\map(f)(\cons(a,x)),\map(\map(f))(\tails(x))) \\
 & = & \map(\map(f))(\cons(\cons(a,x),\tails(x))) \\
 & = & \map(\map(f))(\tails(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\tails$ interacts with $\length$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\tails(x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
We proceed by list induction. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\tails(\nil)) \\
 & = & \length(\cons(\nil,\nil)) \\
 & = & \next(\zero) \\
 & = & \next(\length(\nil))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \length(\tails(\cons(a,x))) \\
 & = & \length(\cons(\cons(a,x),\tails(x))) \\
 & = & \next(\length(\tails(x))) \\
 & = & \next(\next(\length(x)) \\
 & = & \next(\length(\cons(a,x)))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

$\tails$ interacts with $\snoc$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $a \in A$ we have $$\tails(\snoc(a,x)) = \snoc(\nil,\map(\snoc(a,-))(\tails(x))).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \snoc(\nil,\map(\snoc(a,-))(\tails(x))) \\
 & = & \snoc(\nil,\map(\snoc(a,-))(\tails(\nil))) \\
 & = & \snoc(\nil,\map(\snoc(a,-))(\cons(\nil,\nil))) \\
 & = & \snoc(\nil,\cons(\snoc(a,\nil),\map(\snoc(a,-))(\nil))) \\
 & = & \snoc(\nil,\cons(\snoc(a,\nil),\nil)) \\
 & = & \cons(\snoc(a,\nil),\snoc(\nil,\nil)) \\
 & = & \cons(\cons(a,\nil),\cons(\nil,\nil)) \\
 & = & \tails(\cons(a,\nil)) \\
 & = & \tails(\snoc(a,\nil)) \\
 & = & \tails(\snoc(a,x))
\end{eqnarray*}$$
as claimed. Suppose now that the equality holds for some $x$ and let $b \in A$. Now
$$\begin{eqnarray*}
 &   & \tails(\snoc(a,\cons(b,x))) \\
 & = & \tails(\cons(b,\snoc(a,x))) \\
 & = & \cons(\cons(b,\snoc(a,x)),\tails(\snoc(a,x))) \\
 & = & \cons(\cons(b,\snoc(a,x)),\snoc(\nil,\map(\snoc(a,-))(\tails(x)))) \\
 & = & \snoc(\nil,\cons(\cons(b,\snoc(a,x)),\map(\snoc(a,-))(\tails(x)))) \\
 & = & \snoc(\nil,\cons(\snoc(a,\cons(b,x)),\map(\snoc(a,-))(\tails(x)))) \\
 & = & \snoc(\nil,\map(\snoc(a,-))(\cons(\cons(b,x),\tails(x)))) \\
 & = & \snoc(\nil,\map(\snoc(a,-))(\tails(\cons(b,x))))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\tails$ distributes over $\lcs$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$, we have the following.

1. $\lcs(\cons(\nil,\nil),\tails(x)) = \cons(\nil,\nil)$.
2. $\tails(\lcs(x,y)) = \lcs(\tails(x),\tails(y))$.
</p></div>

<div class="proof"><p>
1. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \lcs(\cons(\nil,\nil),\tails(x)) \\
 & = & \lcs(\cons(\nil,\nil),\cons(\nil,\nil)) \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now $\lcs(\cons(\nil,\nil),\tails(x)) = \cons(\nil,\nil)$, so that $\tails(x) = \cat(w,\cons(\nil,\nil))$ for some $w$. Now
$$\begin{eqnarray*}
 &   & \tails(\cons(a,x)) \\
 & = & \cons(\cons(a,x),\tails(x)) \\
 & = & \cons(\cons(a,x),\cat(w,\cons(\nil,\nil))) \\
 & = & \cat(\cons(\cons(a,x),w),\cons(\nil,\nil))),
\end{eqnarray*}$$
and thus $$\lcs(\cons(\nil,\nil),\cons(a,x)) = \cons(\nil,\nil)$$ as claimed.
2. We proceed by list induction on $\length(x)$. For the base case $\length(x) = \zero$ we have $x = \nil$. Then (using (1))
$$\begin{eqnarray*}
 &   & \tails(\lcs(x,y)) \\
 & = & \tails(\lcs(\nil,y)) \\
 & = & \tails(\nil) \\
 & = & \cons(\nil,\nil) \\
 & = & \lcs(\cons(\nil,\nil),\tails(y)) \\
 & = & \lcs(\tails(\nil),\tails(y)) \\
 & = & \lcs(\tails(x),\tails(y))
\end{eqnarray*}$$
as claimed. For the inductive step, suppose the equality holds for all $y$ whenever $\length(x) = n$, and suppose we have $x \in \lists{A}$ with $\length(x) = \next(n)$. Note that $x =\cons(a,v) \neq \nil$ for some $v$ with $\length(v) = n$; in particular $x = \cons(a,v) = \snoc(d,u)$ for some $u$ and $d$ with $\length(u) = n$. We consider two cases for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \tails(\lcs(x,y)) \\
 & = & \tails(\lcs(x,\nil)) \\
 & = & \tails(\nil) \\
 & = & \cons(\nil,\nil) \\
 & = & \lcs(\tails(x),\cons(\nil,\nil)) \\
 & = & \lcs(\tails(x),\tails(\nil)) \\
 & = & \lcs(\tails(x),\tails(y))
\end{eqnarray*}$$
as claimed. Suppose then that $y \neq \nil$; then we have $y = \snoc(b,w)$ for some $b \in A$ and $w \in \lists{A}$. Suppose $d = b$. Note that the function $\snoc(d,-) = \cat(-,\cons(d,\nil))$ in injective. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \tails(\lcs(x,y)) \\
 & = & \tails(\lcs(\snoc(d,u),\snoc(b,w))) \\
 & = & \tails(\snoc(d,\lcs(u,w))) \\
 & = & \snoc(\nil,\map(\snoc(d,-))(\tails(\lcs(u,w)))) \\
 & = & \snoc(\nil,\map(\snoc(d,-))(\lcs(\tails(u),\tails(w)))) \\
 & = & \snoc(\nil,\lcs(\map(\snoc(d,-))(\tails(u)),\map(\snoc(d,-))(\tails(w)))) \\
 & = & \lcs(\snoc(\nil,\map(\snoc(d,-))(\tails(u))),\snoc(\nil,\map(\snoc(d,-))(\tails(w)))) \\
 & = & \lcs(\tails(\snoc(d,u)),\tails(\snoc(d,w))) \\
 & = & \lcs(\tails(\snoc(d,u)),\tails(\snoc(b,w))) \\
 & = & \lcs(\tails(x),\tails(y))
\end{eqnarray*}$$
as needed. Now suppose $d \neq b$. In this case we have
$$\begin{eqnarray*}
 &   & \lcs(\tails(x),\tails(y)) \\
 & = & \lcs(\tails(\snoc(d,u)),\tails(\snoc(b,w))) \\
 & = & \lcs(\snoc(\nil,\map(\snoc(d,-))(\tails(u))),\snoc(\nil,\map(\snoc(b,-))(\tails(w)))) \\
 & = & \snoc(\nil,\lcs(\map(\snoc(d,-))(\tails(u)),\map(\snoc(b,-))(\tails(w)))) \\
 & = & \snoc(\nil,Q).
\end{eqnarray*}$$
Consider this $Q$. If $Q \neq \nil$, that is, $Q = \cons(h,p)$ for some $h$ and $p$, note that $$\snoc(d,q) = h = \snoc(b,q')$$ for some $q$ and $q'$. But $d \neq b$ -- a contradiction. So in fact $Q = \nil$, and we have
$$\begin{eqnarray*}
 &   & \snoc(\nil,Q) \\
 & = & \snoc(\nil,\nil) \\
 & = & \cons(\nil,\nil) \\
 & = & \tails(\nil) \\
 & = & \tails(\lcs(\snoc(d,u),\snoc(b,w))) \\
 & = & \tails(\lcs(x,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Next we'll define $\inits$ in terms of $\tails$.

<div class="result">
<div class="thm"><p>
Let $A$ be a sets. We define $\inits : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\inits(x) = \rev(\map(\rev)(\tails(\rev(x)))).$$
</p></div>
</div>

In Haskell:

> inits :: (List t) => t a -> t (t a)
> inits = rev . map rev . tails . rev

$\inits$ interacts with $\map$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $f : A \rightarrow B$. For all $x \in \lists{A}$, we have $$\inits(\map(f)(x)) = \map(\map(f))(\inits(x)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \inits(\map(f)(x)) \\
 & = & \rev(\map(\rev)(\tails(\rev(\map(f)(x))))) \\
 & = & \rev(\map(\rev)(\tails(\map(f)(\rev(x)))) \\
 & = & \rev(\map(\rev)(\map(\map(f))(\tails(\rev(x))))) \\
 & = & \rev(\map(\rev \circ \map(f))(\tails(\rev(x)))) \\
 & = & \rev(\map(\map(f) \circ \rev)(\tails(\rev(x)))) \\
 & = & \rev(\map(\map(f))(\map(\rev)(\tails(\rev(x))))) \\
 & = & \map(\map(f))(\rev(\map(\rev)(\tails(\rev(x))))) \\
 & = & \map(\map(f))(\inits(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\length(\inits(x)) = \next(\length(x)).$$
</p></div>

<div class="proof"><p>
Note that
$$\begin{eqnarray*}
 &   & \length(\inits(x)) \\
 & = & \length(\rev(\map(\rev)(\tails(\rev(x))))) \\
 & = & \length(\map(\rev)(\tails(\rev(x)))) \\
 & = & \length(\tails(\rev(x))) \\
 & = & \next(\length(\rev(x))) \\
 & = & \next(\length(x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

Finally, $\inits$ distributes over $\lcp$.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x,y \in \lists{A}$, we have $$\inits(\lcp(x,y)) = \lcp(\inits(x),\inits(y)).$$
</p></div>

<div class="proof"><p>
Note that $\rev$ is injective. Now
$$\begin{eqnarray*}
 &   & \lcp(\inits(x),\inits(y)) \\
 & = & \lcp(\rev(\map(\rev)(\tails(\rev(x)))),\rev(\map(\rev)(\tails(\rev(y))))) \\
 & = & \rev(\lcs(\map(\rev)(\tails(\rev(x))),\map(\rev)(\tails(\rev(y))))) \\
 & = & \rev(\map(\rev)(\lcs(\tails(\rev(x)),\tails(\rev(y))))) \\
 & = & \rev(\map(\rev)(\tails(\lcs(\rev(x),\rev(y))))) \\
 & = & \rev(\map(\rev)(\tails(\rev(\lcp(x,y))))) \\
 & = & \inits(\lcp(x,y))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\tails$ and $\inits$:

> -- tails(x) == tails'(x)
> _test_tails_alt :: (List t, Equal a)
>   => t a -> ListOf t a -> Bool
> _test_tails_alt _ x =
>   (tails x) ==== (tails' x)
> 
> 
> -- tails(map(f)(x)) == map(map(f))(tails(x))
> _test_tails_map :: (List t, Equal a)
>   => t a -> (a -> a) -> ListOf t a -> Bool
> _test_tails_map _ f x =
>   (tails (map f x)) ==== (map (map f) (tails x))
> 
> 
> -- length(tails(x)) == next(length(x))
> _test_tails_length :: (List t, Equal a, Natural n)
>   => t a -> n -> ListOf t a -> Bool
> _test_tails_length _ n x =
>   let
>     lx = length x `withTypeOf` Nat n
>   in
>     (length (tails x)) ==== (next lx)
> 
> 
> -- tails(snoc(a,x)) == snoc(nil,map(snoc(a,-))(tails(x)))
> _test_tails_snoc :: (List t, Equal a)
>   => t a -> a -> ListOf t a -> Bool
> _test_tails_snoc _ a x =
>   (tails (snoc a x)) ==== (snoc nil (map (snoc a) (tails x)))
> 
> 
> -- tails(lcs(x,y)) == lcs(tails(x),tails(y))
> _test_tails_lcs :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_tails_lcs _ x y =
>   (tails (lcs x y)) ==== (lcs (tails x) (tails y))
> 
> 
> -- inits(map(f)(x)) == map(map(f))(inits(x))
> _test_inits_map :: (List t, Equal a)
>   => t a -> (a -> a) -> ListOf t a -> Bool
> _test_inits_map _ f x =
>   (inits (map f x)) ==== (map (map f) (inits x))
> 
> 
> -- length(inits(x)) == next(length(x))
> _test_inits_length :: (List t, Equal a, Natural n)
>   => t a -> n -> ListOf t a -> Bool
> _test_inits_length _ n x =
>   let
>     lx = length x `withTypeOf` Nat n
>   in
>     (length (inits x)) ==== (next lx)
> 
> 
> -- inits(lcp(x,y)) == lcp(inits(x),inits(y))
> _test_inits_lcp :: (List t, Equal a)
>   => t a -> ListOf t a -> ListOf t a -> Bool
> _test_inits_lcp _ x y =
>   (inits (lcp x y)) ==== (lcp (inits x) (inits y))

And the suite:

> -- run all tests for tails and inits
> _test_tails_inits ::
>   ( Show a, Equal a, Arbitrary a, CoArbitrary a
>   , Natural n
>   , List t
>   ) => String -> t a -> n -> Int -> Int -> IO ()
> _test_tails_inits label t n maxSize numCases = do
>   testLabel ("tails & inits: " ++ label)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_tails_alt t)
>   runTest args (_test_tails_map t)
>   runTest args (_test_tails_length t n)
>   runTest args (_test_tails_snoc t)
>   runTest args (_test_tails_lcs t)
> 
>   runTest args (_test_inits_map t)
>   runTest args (_test_inits_length t n)
>   runTest args (_test_inits_lcp t)

And ``main``:

> main_tails_inits :: IO ()
> main_tails_inits = do
>   _test_tails_inits "ConsList Bool & Unary"  (nil :: ConsList Bool) (zero :: Unary) 20 100
>   _test_tails_inits "ConsList Unary & Unary" (nil :: ConsList Unary) (zero :: Unary) 20 100
