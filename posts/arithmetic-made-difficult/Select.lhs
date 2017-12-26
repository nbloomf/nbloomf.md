---
title: Select
author: nbloomf
date: 2017-05-25
tags: arithmetic-made-difficult, literate-haskell
---

> module Select
>   ( select, _test_select, main_select
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
> import Sublist
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
3. $\select(\next(n),\cons(a,x)) = \cat(\map(\cons(a,-))(\select(n,x)),\select(\next(n),x))$.
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

$\length$:

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

$\sublist$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set and let $x,y \in \lists{A}$. If $\sublist(x,y) = \btrue$, then $\sublist(\select(k,x),\select(k,y)) = \btrue$ for all $k \in \nats$.
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, suppose $\sublist(x,y) = \btrue$. Now
$$\begin{eqnarray*}
 &   & \sublist(\select(k,x),\select(k,y)) \\
 & = & \sublist(\select(\zero,x),\select(\zero,y)) \\
 & = & \sublist(\cons(\nil,\nil),\cons(\nil,\nil)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for some $k$. We now proceed by list induction on $y$. For the base case $y = \nil$, suppose $$\btrue = \sublist(x,y) = \sublist(x,\nil);$$ then we must have $x = \nil$. In this case we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),y)) \\
 & = & \sublist(\select(\next(k),\nil),\select(\next(k),\nil)) \\
 & = & \sublist(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the implication holds for $\next(k)$ and all $x$ for some $y$, and let $b \in A$. Suppose further that $\sublist(x,\cons(b,y)) = \btrue$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\nil),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\nil,\select(\next(k),\cons(b,y))) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,u)$. We have two possibilities. If $a \neq b$, then since $$\btrue = \sublist(x,\cons(b,y)) = \sublist(\cons(a,u),\cons(b,y))$$ we have $\btrue = \sublist(\cons(a,u),y) = \sublist(x,y)$. By the inductive hypothesis on $y$ we have $$\sublist(\select(\next(k),x),\select(\next(k),y)) = \btrue.$$ Moreover, note that
$$\begin{eqnarray*}
 &   & \select(\next(k),\cons(b,y)) \\
 & = & \cat(\map(\cons(b,-))(\select(k,y)),\select(\next(k),y))
\end{eqnarray*}$$
so that, in particular, $$\sublist(\select(\next(k),y),\select(\next(k),\cons(b,y))) = \btrue.$$ Since $\sublist$ is transitive, we have $$\sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) = \btrue$$ as needed.

Suppose instead that $a = b$. Then since $$\btrue = \sublist(x,\cons(b,y)) = \sublist(\cons(a,u),\cons(b,y)),$$ in fact we have $\sublist(u,y) = \btrue$. Using the inductive hypothesis on $k$, we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(u,y) \\
 & = & \sublist(\select(k,u),\select(k,y)) \\
 & = & \sublist(\map(\cons(a,-))(\select(k,u)),\map(\cons(a,-))(\select(k,y))) \\
 & = & \sublist(H,K)
\end{eqnarray*}$$
and similarly using the inductive hypothesis on $y$ we have
$$\begin{eqnarray*}
 &   & \btrue \\
 & = & \sublist(u,y) \\
 & = & \sublist(\select(\next(k),u),\select(\next(k),y)) \\
 & = & \sublist(P,Q).
\end{eqnarray*}$$
Now we have
$$\begin{eqnarray*}
 &   & \sublist(\select(\next(k),x),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\cons(a,u)),\select(\next(k),\cons(b,y))) \\
 & = & \sublist(\select(\next(k),\cons(a,u)),\select(\next(k),\cons(a,y))) \\
 & = & \sublist(\cat(\map(\cons(a,-))(\select(k,u)),\select(\next(k),u)),\cat(\map(\cons(a,-))(\select(k,y)),\select(\next(k),y))) \\
 & = & \sublist(\cat(H,P),\cat(K,Q)) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Selections are sublists:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$ and $k \in \nats$. Then $$\all(\sublist(-,x),\select(k,x)) = \btrue.$$
</p></div>

<div class="proof"><p>
We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(k,x)) \\
 & = & \all(\sublist(-,x),\select(\zero,x)) \\
 & = & \all(\sublist(-,x),\cons(\nil,\nil)) \\
 & = & \band(\sublist(\nil,x),\all(\sublist(-,x),\nil)) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose instead that $k = \next(m)$; we proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(k,x)) \\
 & = & \all(\sublist(-,\nil),\select(\next(m),\nil)) \\
 & = & \all(\sublist(-,\nil),\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$ and let $a \in A$. Using the inductive hypothesis we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\map(\cons(a,-))(\select(m,x))) \\
 & = & \all(\sublist(-,\cons(a,x)) \circ \cons(a,-),\select(m,x)) \\
 & = & \all(\sublist(\cons(a,-),\cons(a,x)),\select(m,x)) \\
 & = & \all(\sublist(-,x),\select(m,x)) \\
 & = & \btrue.
\end{eqnarray*}$$
Also using the inductive hypothesis, we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,x),\select(\next(m),x)) \\
 & = & \btrue,
\end{eqnarray*}$$
and for all $u \in \lists{A}$, if $\sublist(u,x) = \btrue$ then $\sublist(u,\cons(a,x)) = \btrue$. Thus we have
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\select(\next(m),x)) \\
 & = & \btrue.
\end{eqnarray*}$$
 Now
$$\begin{eqnarray*}
 &   & \all(\sublist(-,\cons(a,x)),\select(k,\cons(a,x))) \\
 & = & \all(\sublist(-,\cons(a,x)),\select(\next(m),\cons(a,x))) \\
 & = & \all(\sublist(-,\cons(a,x)),\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \band(\all(\sublist(-,\cons(a,x)),\map(\cons(a,-))(\select(m,x))),\all(\sublist(-,\cons(a,x)),\select(\next(m),x))) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Selections have fixed length:

<div class="result">
<div class="thm"><p>
Let $A$ be a set with $x \in \lists{A}$ and $k \in \nats$. Then $$\all(\beq(k,\length(-)),\select(k,x)) = \btrue.$$
</p></div>

<div class="proof"><p>
We consider two possibilities for $k$. If $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,x)) \\
 & = & \all(\beq(\zero,\length(-)),\select(\zero,x)) \\
 & = & \all(\beq(\zero,\length(-)),\cons(\nil,\nil)) \\
 & = & \band(\beq(\zero,\length(\nil)),\all(\beq(\zero,\length(-)),\nil)) \\
 & = & \band(\beq(\zero,\zero),\btrue) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as claimed. Suppose instead that $k = \next(m)$. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,x)) \\
 & = & \all(\beq(k,\length(-)),\select(\next(m),\nil)) \\
 & = & \all(\beq(k,\length(-)),\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $k$ for some $x$ and let $a \in A$. Using the inductive hypothesis (twice!) we have
$$\begin{eqnarray*}
 &   & \all(\beq(k,\length(-)),\select(k,\cons(a,x))) \\
 & = & \all(\beq(k,\length(-)),\select(\next(m),\cons(a,x))) \\
 & = & \all(\beq(k,\length(-)),\cat(\map(\cons(a,-))(\select(m,x)),\select(\next(m),x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\all(\beq(k,\length(-)),\select(\next(m),x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\all(\beq(k,\length(-)),\select(k,x))) \\
 & = & \band(\all(\beq(k,\length(-)),\map(\cons(a,-))(\select(m,x))),\btrue) \\
 & = & \band(\all(\beq(k,\length(-) \circ \cons(a,-)),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(k,\length(\cons(a,-))),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(\next(m),\next(\length(-))),\select(m,x)),\btrue) \\
 & = & \band(\all(\beq(m,\length(-)),\select(m,x)),\btrue) \\
 & = & \band(\btrue,\btrue) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\select$:

> _test_select_zero :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> Bool)
> _test_select_zero _ n =
>   testName "select(zero,x) == cons(nil,nil)" $
>   \x -> let
>     zero' = zero `withTypeOf` n
>   in
>     eq (select zero' x) (cons nil nil)
> 
> 
> _test_select_nil :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (n -> Bool)
> _test_select_nil t _ =
>   testName "select(k,nil) == if k == 0 then cons(nil,nil) else nil" $
>   \k -> let
>     nil' = nil `withTypeOf` (ListOf t)
>   in
>     if isZero k
>       then eq (select k nil') (cons nil nil)
>       else eq (select k nil') nil
> 
> 
> _test_select_one :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (ListOf t a -> Bool)
> _test_select_one _ n =
>   testName "select(next(zero),x) == map(cons(-,nil))(x)" $
>   \x -> let
>     one' = (next zero) `withTypeOf` n
>   in
>     eq (select one' x) (map (\a -> cons a nil) x)
> 
> 
> _test_select_length :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (n -> ListOf t a -> Bool)
> _test_select_length _ _ =
>   testName "length(select(k,x)) == choose(length(x),k)" $
>   \k x -> eq (length (select k x)) (choose (length x) k)
> 
> 
> _test_select_sublist :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (n -> ListOf t a -> ListOf t a -> Bool)
> _test_select_sublist _ _ =
>   testName "sublist(x,y) == sublist(select(k,x),select(k,y))" $
>   \k x y -> if eq (sublist x y) True
>     then eq (sublist (select k x) (select k y)) True
>     else True
> 
> 
> _test_select_all_sublist :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (n -> ListOf t a -> Bool)
> _test_select_all_sublist _ _ =
>   testName "all(sublist(-,x),select(k,x))" $
>   \k x -> all (\u -> sublist u x) (select k x)
> 
> 
> _test_select_all_length :: (List t, Equal a, Natural n)
>   => t a -> n -> Test (n -> ListOf t a -> Bool)
> _test_select_all_length _ _ =
>   testName "all(eq(k,length(-)),select(k,x))" $
>   \k x -> all (\u -> eq k (length u)) (select k x)

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
>   runTest args (_test_select_sublist t n)
>   runTest args (_test_select_all_sublist t n)
>   runTest args (_test_select_all_length t n)

And ``main``:

> main_select :: IO ()
> main_select = do
>   _test_select (nil :: ConsList Bool)  (zero :: Unary) 20 30
>   _test_select (nil :: ConsList Unary) (zero :: Unary) 20 30
