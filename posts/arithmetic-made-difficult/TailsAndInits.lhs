---
title: Tails and Inits
author: nbloomf
date: 2017-05-12
tags: arithmetic-made-difficult, literate-haskell
slug: tails-inits
---

> module TailsAndInits
>   ( tails, inits, _test_tails_inits, main_tails_inits
>   ) where
> 
> import Prelude ()
> import Booleans
> import NaturalNumbers
> import Lists
> import HeadAndTail
> import ConsumingFold
> import Snoc
> import Reverse
> import Length
> import Map
> import Cat
> import Zip
> import Prefix
> import LongestCommonPrefix
> import AllAndAny

Today we'll construct the lists of all suffixes ($\tails$) and prefixes ($\inits$) of a list. Starting with $\tails$: this function should have a signature like $$\lists{A} \rightarrow \lists{\lists{A}}.$$

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Let $\gamma = \cons(\nil,\nil)$, and define $\sigma : A \times \lists{A} \times \lists{\lists{A}} \rightarrow \lists{\lists{A}}$ by $$\sigma(a,x,z) = \cons(\cons(a,x),z).$$ Now define $\tails : \lists{A} \rightarrow \lists{\lists{A}}$ by $$\tails = \cfoldr{\gamma}{\sigma}.$$

In Haskell:

> tails :: (List t) => t a -> t (t a)
> tails = cfoldr gamma sigma
>   where
>     gamma = cons nil nil
>     sigma a x z = cons (cons a x) z

</p></div>
</div>

Since $\tails$ is defined as a $\cfoldr{\ast}{\ast}$, it is the unique solution to a system of functional equations.

<div class="result">
<div class="corollary"><p>
Let $A$ be a set. $\tails$ is the unique map $f : \lists{A} \rightarrow \lists{\lists{A}}$ which satisfies the following equations for all $a \in A$ and $x \in \lists{A}$.
$$\left\{\begin{array}{l}
 f(\nil) = \cons(\nil,\nil) \\
 f(\cons(a,x)) = \cons(\cons(a,x),f(x))
\end{array}\right.$$
</p></div>

<div class="test"><p>

> _test_tails_nil :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test Bool
> _test_tails_nil t =
>   testName "tails(nil) == cons(nil,nil)" $
>   eq (tails (nil `withTypeOf` t)) (cons nil nil)
> 
> 
> _test_tails_cons :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_tails_cons _ =
>   testName "tails(cons(a,x)) == cons(cons(a,x),tails(x))" $
>   \a x -> eq (tails (cons a x)) (cons (cons a x) (tails x))

</p></div>
</div>

(@@@)

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
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\length(\tails(x)) = \next(\length(x)).$$ In particular, $\tails{x} \neq \nil$.
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

And $\tails$ consists of suffixes.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ we have $$\all(\suffix(-,x),\tails(x)) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \all(\suffix(-,x),\tails(x)) \\
 & = & \all(\suffix(-,\nil),\cons(\nil,\nil)) \\
 & = & \band(\suffix(\nil,\nil),\all(\suffix(-,\nil),\nil)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Note that if $\suffix(u,x) = \btrue$ then $\suffix(u,\cons(a,x)) = \btrue$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \all(\suffix(-,x),\tails(x)) \\
 & = & \all(\suffix(-,\cons(a,x)),\tails(x)) \\
 & = & \band(\btrue,\all(\suffix(-,\cons(a,x)),\tails(x)) \\
 & = & \band(\suffix(\cons(a,x),\cons(a,x)),\all(\suffix(-,\cons(a,x)),\tails(x)))) \\
 & = & \all(\suffix(-,\cons(a,x)),\cons(\cons(a,x),\tails(x))) \\
 & = & \all(\suffix(-,\cons(a,x)),\tails(\cons(a,x)))
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

> 
> 
> _test_tails_map :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_tails_map _ =
>   testName "tails(map(f)(x)) == map(map(f))(tails(x))" $
>   \f x -> eq (tails (map f x)) (map (map f) (tails x))
> 
> 
> _test_tails_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (t a -> Bool)
> _test_tails_length _ n =
>   testName "length(tails(x)) == next(length(x))" $
>   \x -> let
>     lx = length x `withTypeOf` n
>   in
>     eq (length (tails x)) (next lx)
> 
> 
> _test_tails_snoc :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test (a -> t a -> Bool)
> _test_tails_snoc _ =
>   testName "tails(snoc(a,x)) == snoc(nil,map(snoc(a,-))(tails(x)))" $
>   \a x -> eq (tails (snoc a x)) (snoc nil (map (snoc a) (tails x)))
> 
> 
> _test_tails_lcs :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> Test (t a -> t a -> Bool)
> _test_tails_lcs _ =
>   testName "tails(lcs(x,y)) == lcs(tails(x),tails(y))" $
>   \x y -> eq (tails (lcs x y)) (lcs (tails x) (tails y))
> 
> 
> _test_inits_map :: (List t, Equal a, Equal (t (t a)))
>   => t a -> Test ((a -> a) -> t a -> Bool)
> _test_inits_map _ =
>   testName "inits(map(f)(x)) == map(map(f))(inits(x))" $
>   \f x -> eq (inits (map f x)) (map (map f) (inits x))
> 
> 
> _test_inits_length :: (List t, Equal a, Natural n, Equal n)
>   => t a -> n -> Test (t a -> Bool)
> _test_inits_length _ n =
>   testName "length(inits(x)) == next(length(x))" $
>   \x -> let
>     lx = length x `withTypeOf` n
>   in
>     eq (length (inits x)) (next lx)
> 
> 
> _test_inits_lcp :: (List t, Equal a, Equal (t a), Equal (t (t a)))
>   => t a -> Test (t a -> t a -> Bool)
> _test_inits_lcp _ =
>   testName "inits(lcp(x,y)) == lcp(inits(x),inits(y))" $
>   \x y -> eq (inits (lcp x y)) (lcp (inits x) (inits y))

And the suite:

> _test_tails_inits ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName n, Natural n, Equal n
>   , TypeName (t a), List t
>   , Show (t a), Equal (t a), Arbitrary (t a), Equal (t (a,a)), Equal (t (t a))
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_tails_inits t n maxSize numCases = do
>   testLabel ("tails & inits: " ++ typeName t ++ " & " ++ typeName n)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_tails_nil t)
>   runTest args (_test_tails_cons t)
> 
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
>   _test_tails_inits (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_tails_inits (nil :: ConsList Unary) (zero :: Unary) 20 100
