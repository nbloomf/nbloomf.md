---
title: Select
author: nbloomf
date: 2017-05-25
tags: arithmetic-made-difficult, literate-haskell
---

> module Select
>   ( _test_select, main_select
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import Plus
> import Choose
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
> 
> import Prelude ()
> import Test.QuickCheck hiding (choose)
> import Text.Show.Functions

Today we'll define a function, $\select$, which takes a natural number $n$ and a list $x$ and constructs the list of all length $n$ sublists of $x$. The signature of $\select$ should be $$\nats \times \lists{A} \rightarrow \lists{\lists{A}},$$ which matches several of our recursion operators. Which one to use? We'll try a right fold first -- to make the types work out, we have to say $$\select(n,x) = \foldr{\varepsilon}{\varphi}(x)(n)$$ for some appropriate $\varepsilon$ and $\varphi$. Now $\varepsilon$ needs to have signature $$\varepsilon : \nats \rightarrow \lists{\lists{A}}$$ and $\varphi$ should have signature $$\varphi : A \times \lists{\lists{A}}^\nats \rightarrow \nats \rightarrow \lists{\lists{A}}.$$

But what should $\varepsilon$ and $\varphi$ be? First, let's think about what $\select(n,\nil)$ means. The nil list has no positive length sublists, so we expect that
$$\begin{eqnarray*}
 &   & \nil \\
 & = & \select(\next(n),\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(\next(n)) \\
 & = & \varepsilon(\next(n)).
\end{eqnarray*}$$
But the nil list has exactly one length zero sublist, namely $\nil$. So we also expect that
$$\begin{eqnarray*}
 &   & \cons(\nil,\nil) \\
 & = & \select(\zero,\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(\zero) \\
 & = & \varepsilon(\zero).
\end{eqnarray*}$$
Now let's think about $\select(n,\cons(a,x))$. Every list (particularly every non-nil list) has exactly one length zero sublist, namely $\nil$. So we expect that
$$\begin{eqnarray*}
 &   & \cons(\nil,\nil) \\
 & = & \select(\zero,\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\zero) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\zero).
\end{eqnarray*}$$
Meanwhile, the length $\next(n)$ sublists of $\cons(a,x)$ come in two flavors: those of the form $\cons(a,u)$ where $u$ is a length $n$ sublist of $x$, and the length $\next(n)$ sublists of $x$. So we expect that
$$\begin{eqnarray*}
 &   & \cat(\map(\cons(a,-))(\select(n,x)),\select(\next(n),x) \\
 & = & \select(\next(n),\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\next(n)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\next(n)) \\
 & = & \varphi(a,\select(-,x))(\next(n)).
\end{eqnarray*}$$
With this in mind, we define $\select$ as follows.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\varepsilon : \nats \rightarrow \lists{\lists{A}}$ by $$\varepsilon(k) = \bif{\iszero(k)}{\cons(\nil,\nil)}{\nil}$$ and define $\varphi : A \times \lists{\lists{A}}^\nats \rightarrow \nats \rightarrow \lists{\lists{A}}$ by $$\varphi(a,f)(k) = \bif{\iszero(k)}{\cons(\nil,\nil)}{\cat(\map(\cons(a,-))(f(\prev(k))),f(k))}.$$ Now define $\select : \nats \times \lists{A} \rightarrow \lists{\lists{A}}$ by $$\select(n,x) = \foldr{\varepsilon}{\varphi}(x)(n).$$

In Haskell:

> select :: (List t, Natural n) => n -> t a -> t (t a)
> select n x = foldr epsilon phi x n
>   where
>     epsilon k = if isZero k
>       then cons nil nil
>       else nil
> 
>     phi a f n = case natShape n of
>       Zero   -> cons nil nil
>       Next k -> cat (map (cons a) (f k)) (f n)

</p></div>
</div>

Let's make sure $\select$ does what we expected.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $n \in \nats$, $a \in A$, and $x \in \lists{A}$ we have the following.

1. $\select(n,\nil) = \bif{\iszero(n)}{\cons(\nil,\nil)}{\nil}$.
2. $\select(\zero,\cons(a,x)) = \cons(\nil,\nil)$.
3. $\select(\next(n),\cons(a,x)) = \cat(\map(\cons(a,-))(\select(n,x),\select(\next(n),x))$.
</p></div>

<div class="proof"><p>
1. Note that
$$\begin{eqnarray*}
 &   & \select(n,\nil) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(n) \\
 & = & \varepsilon(n) \\
 & = & \bif{\iszero(n)}{\cons(\nil,\nil)}{\nil}
\end{eqnarray*}$$
as claimed.
2. Note that
$$\begin{eqnarray*}
 &   & \select(\zero,\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\zero) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\zero) \\
 & = & \cons(\nil,\nil)
\end{eqnarray*}$$
as claimed.
3. Note that
$$\begin{eqnarray*}
 &   & \select(\next(n),\cons(a,x)) \\
 & = & \foldr{\varepsilon}{\varphi}(\cons(a,x))(\next(n)) \\
 & = & \varphi(a,\foldr{\varepsilon}{\varphi}(x))(\next(n)) \\
 & = & \cat(\map(\cons(a,-))(\foldr{\varepsilon}{\varphi}(x)(n)),\foldr{\varepsilon}{\varphi}(x)(\next(n)) \\
 & = & \cat(\map(\cons(a,-))(\select(n,x)),\select(\next(n),x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

A special case.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$, we have $$\select(\next(\zero),x) = \map(\cons(-,\nil))(x).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \select(\next(\zero),x) \\
 & = & \select(\next(\zero),\nil) \\
 & = & \bif{\isnil(\next(\zero))}{\cons(\nil,\nil)}{\nil} \\
 & = & \nil \\
 & = & \map(\cons(-,\nil))(\nil) \\
 & = & \map(\cons(-,\nil))(x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \select(\next(\zero),\cons(a,x)) \\
 & = & \cat(\map(\cons(a,-))(\select(\zero,x)),\select(\next(\zero),x)) \\
 & = & \cat(\map(\cons(a,-))(\cons(\nil,\nil)),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\cons(\cons(a,\nil),\map(\cons(a,-))(\nil)),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\cons(\cons(a,\nil),\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\snoc(\cons(a,\nil),\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cat(\nil,\cons(\cons(a,\nil),\map(\cons(-,\nil))(x))) \\
 & = & \cons(\cons(a,\nil),\map(\cons(-,\nil))(x)) \\
 & = & \cons(\cons(-,\nil)(a),\map(\cons(-,\nil))(x)) \\
 & = & \map(\cons(-,\nil))(\cons(a,x))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$. For all $k \in \nats$, we have $$\length(\select(k,x)) = \nchoose(\length(x),k).$$
</p></div>

<div class="proof"><p>
We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\select(k,x)) \\
 & = & \length(\select(k,\nil)) \\
 & = & \length(\bif{\iszero(k)}{\cons(\nil,\nil)}{\nil}) \\
 & = & \bif{\iszero(k)}{\length(\cons(\nil,\nil))}{\length(\nil)} \\
 & = & \bif{\iszero(k)}{\next(\zero)}{\zero} \\
 & = & \nchoose(\zero,k) \\
 & = & \nchoose(\length(\nil),k) \\
 & = & \nchoose(\length(x),k)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\select(k,\cons(a,x))) \\
 & = & \length(\select(\zero,\cons(a,x))) \\
 & = & \length(\cons(\nil,\nil)) \\
 & = & \next(\zero) \\
 & = & \nchoose(\next(\length(x)),\zero) \\
 & = & \nchoose(\length(\cons(a,x)),k)
\end{eqnarray*}$$
as needed. If $k = \next(m)$, then using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \length(\select(k,\cons(a,x))) \\
 & = & \length(\select(\next(m),\cons(a,x))) \\
 & = & \length(\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \nplus(\length(\map(\cons(a,-))(\select(m,x))),\length(\select(\next(m),x))) \\
 & = & \nplus(\length(\select(m,x)),\length(\select(\next(m),x))) \\
 & = & \nplus(\nchoose(\length(x),m),\nchoose(\length(x),\next(m))) \\
 & = & \nplus(\nchoose(\length(x),\next(m)),\nchoose(\length(x),m)) \\
 & = & \nchoose(\next(\length(x)),\next(m)) \\
 & = & \nchoose(\length(\cons(a,x)),k)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>

<div class="result">
<div class="defn"><p>

</p></div>
</div>

<div class="result">
<div class="thm"><p>

</p></div>

<div class="proof"><p>

</p></div>
</div>


Testing
-------

Here are our property tests for $\select$:

> -- select(zero,x) == cons(nil,nil)
> _test_select_zero :: (List t, Equal a, Natural n)
>   => t a -> n -> ListOf t a -> Bool
> _test_select_zero _ n x =
>    let
>      zero' = zero `withTypeOf` n
>    in
>      (select zero' x) ==== (cons nil nil)
> 
> 
> -- select(k,nil) == if k == 0 then cons(nil,nil) else nil
> _test_select_nil :: (List t, Equal a, Natural n)
>   => t a -> n -> Nat n -> Bool
> _test_select_nil t _ k =
>    let
>      nil' = nil `withTypeOf` (ListOf t)
>    in
>      if isZero k
>        then (select k nil') ==== (cons nil nil)
>        else (select k nil') ==== nil
> 
> 
> -- select(next(zero),x) == map(cons(-,nil))(x)
> _test_select_one :: (List t, Equal a, Natural n)
>   => t a -> n -> ListOf t a -> Bool
> _test_select_one _ n x =
>    let
>      one' = (next zero) `withTypeOf` n
>    in
>      (select one' x) ==== (map (\a -> cons a nil) x)
> 
> 
> -- length(select(k,x)) == choose(length(x),k)
> _test_select_length :: (List t, Equal a, Natural n)
>   => t a -> n -> Nat n -> ListOf t a -> Bool
> _test_select_length _ _ k x =
>    (length (select k x)) ==== (choose (length x) k)

And the suite:

> -- run all tests for select
> _test_select ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName n, Natural n, Show n, Arbitrary n
>   , TypeName (t a), List t
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_select t n maxSize numCases = do
>   testLabel ("select: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_select_zero t n)
>   runTest args (_test_select_nil t n)
>   runTest args (_test_select_one t n)
>   runTest args (_test_select_length t n)

And ``main``:

> main_select :: IO ()
> main_select = do
>   _test_select (nil :: ConsList Bool)  (zero :: Unary) 20 30
>   _test_select (nil :: ConsList Unary) (zero :: Unary) 20 30
