---
title: Take and Drop
author: nbloomf
date: 2017-05-29
tags: arithmetic-made-difficult, literate-haskell
slug: take-drop
---

> module TakeAndDrop
>   ( take, drop, _test_take_drop, main_take_drop
>   ) where
> 
> import Booleans
> import Tuples
> import NaturalNumbers
> import BailoutRecursion
> import Plus
> import MaxAndMin
> 
> import Lists
> import HeadAndTail
> import Snoc
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

Today we'll define two functions, $\take$ and $\drop$, that split a list at a given index. For example, $\take(3,x)$ should return a list consisting of the first 3 items of $x$. The biggest question to think about is what $\take$ should do if $x$ doesn't have 3 items to take -- should $\take(3,-)$ mean take *exactly* 3 or take *at most* 3? The simplest interpretation is *at most*, since with *exactly* we'd need the return type to encode a failure case. That said, under the *at most* interpretation, the signature of $\take$ will be $$\take : \nats \times \lists{A} \rightarrow \lists{A}.$$ Usually we'd try to define such a function with a fold, but in this case $\unfoldN$ does exactly what we want.

(Fundamentally, $\take$ and $\drop$ compute a kind of "$\cat$-factorization" of a list based on index from the left. This is not the only useful such factorization; we will address two others in future posts.)

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $f : \lists{A} \rightarrow \ast + \lists{A} \times A$ by $$f(x) = \left\{ \begin{array}{ll} \ast & \mathrm{if}\ x = \nil \\ (b,a) & \mathrm{if}\ x = \cons(a,b) \end{array}. \right.$$ We then define $$\take : \nats \times \lists{A} \rightarrow \lists{A}$$ by $$\take(k,x) = \unfoldN(f,k,x).$$

In Haskell:

> take :: (Natural n, List t) => n -> t a -> t a
> take = unfoldN f
>   where
>     f z = case uncons z of
>       Left ()    -> Left ()
>       Right (a,u) -> Right (u,a)

</p></div>
</div>

The following result suggests an alternative implementation.

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x \in \lists{A}$, $a \in A$, and $k \in \nats$. Then we have the following.

1. $\take(\zero,x) = \nil$.
2. $\take(k,\nil) = \nil$.
3. $\take(\next(k),\cons(a,x)) = \cons(a,\take(k,x))$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \take(\zero,x) \\
 & = & \unfoldN(f,\zero,x) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
2. Certainly the equality holds if $k = \zero$. Suppose instead that $k = \next(t)$. Now $$f(\nil) = \ast$$ since $\uncons(\nil) = \ast$, and thus
$$\begin{eqnarray*}
 &   & \take(k,\nil) \\
 & = & \take(\next(t),\nil) \\
 & = & \unfoldN(f,\next(t),\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. Note that $$\uncons(\cons(a,x)) = (a,x).$$ Then we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\cons(a,x)) \\
 & = & \unfoldN(f,\next(k),\cons(a,x)) \\
 & = & \cons(a,\unfoldN(f,k,x)) \\
 & = & \cons(a,\take(k,x))
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> take' :: (Natural n, List t) => n -> t a -> t a
> take' k x = case natShape k of
>   Zero   -> nil
>   Next t -> case uncons x of
>     Left ()     -> nil
>     Right (a,u) -> cons a (take' t u)

Now $\take$ is a prefix:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\prefix(\take(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \prefix(\take(k,x),x) \\
 & = & \prefix(\take(\zero,x),x) \\
 & = & \prefix(\nil,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for all $x$ for some $k$. We now proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \prefix(\take(\next(k),\nil),\nil) \\
 & = & \prefix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the result holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \prefix(\take(\next(k),\cons(a,x)),\cons(a,x)) \\
 & = & \prefix(\cons(a,\take(k,x)),\cons(a,x)) \\
 & = & \prefix(\take(k,x),x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

So $\take$ is a sublist:

<div class="result">
<div class="corollary"><p>
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\sublist(\take(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We have $$\prefix(\take(k,x),x) = \btrue,$$ so $$\infix(\take(k,x),x) = \btrue,$$ so $$\sublist(\take(k,x),x) = \btrue$$ as claimed.
</p></div>
</div>

$\take$ has bounded length:

<div class="result">
<div class="thm"><p>
Let $A$ be a set, with $x \in \lists{A}$ and $k \in \nats$. Then we have $$\length(\take(k,x) = \nmin(k,\length(x)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \length(\take(k,x)) \\
 & = & \length(\take(\zero,x)) \\
 & = & \length(\nil) \\
 & = & \zero \\
 & = & \nmin(\zero,\length(x)) \\
 & = & \nmin(k,\length(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We now proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \length(\take(\next(k),x)) \\
 & = & \length(\take(\next(k),\nil)) \\
 & = & \length(\nil) \\
 & = & \zero \\
 & = & \nmin(\next(k),\zero) \\
 & = & \nmin(\next(k),\length(\nil)) \\
 & = & \nmin(\next(k),\length(x))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now we have
$$\begin{eqnarray*}
 &   & \length(\take(\next(k),\cons(a,x))) \\
 & = & \length(\cons(a,\take(k,x))) \\
 & = & \next(\length(\take(k,x))) \\
 & = & \next(\nmin(k,\length(x))) \\
 & = & \nmin(\next(k),\next(\length(x))) \\
 & = & \nmin(\next(k),\length(\cons(a,x)))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\take$ "distributes over" $\zip$:

<div class="result">
<div class="thm"><p>
Let $A$ and $B$ be sets with $x \in \lists{A}$, $y \in \lists{B}$, and $k \in \nats$. Then $$\zip(\take(k,x),\take(k,y)) = \take(k,\zip(x,y)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(k,x),\take(k,y)) \\
 & = & \zip(\take(\zero,x),\take(\zero,y)) \\
 & = & \zip(\nil,\nil) \\
 & = & \nil \\
 & = & \take(\zero,\zip(x,y)) \\
 & = & \take(k,\zip(x,y))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ and $y$ for some $k$. We consider two possibilities for $x$. If $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),\nil),\take(\next(k),y)) \\
 & = & \zip(\nil,\take(\next(k),y)) \\
 & = & \nil \\
 & = & \take(\next(k),\nil) \\
 & = & \take(\next(k),\zip(\nil,y)) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed. Suppose instead that $x = \cons(a,u)$ for some $u$. We now consider two possibilities for $y$. If $y = \nil$, we have
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),x),\take(\next(k),\nil)) \\
 & = & \zip(\take(\next(k),x),\nil) \\
 & = & \nil \\
 & = & \take(\next(k),\nil) \\
 & = & \take(\next(k),\zip(x,\nil)) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed. Suppose instead that $y = \cons(b,v)$. Now
$$\begin{eqnarray*}
 &   & \zip(\take(\next(k),x),\take(\next(k),y)) \\
 & = & \zip(\take(\next(k),\cons(a,u)),\take(\next(k),\cons(b,v))) \\
 & = & \cons((a,b),\zip(\take(k,u),\take(k,v))) \\
 & = & \cons((a,b),\take(k,\zip(u,v))) \\
 & = & \take(\next(k),\cons((a,b),\zip(u,v))) \\
 & = & \take(\next(k),\zip(\cons(a,u),\cons(b,v))) \\
 & = & \take(\next(k),\zip(x,y))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

$\take$ and $\range$:

<div class="result">
<div class="thm"><p>
For all $a,b,k \in \nats$, we have $$\take(k,\range(a,b)) = \range(a,\nmin(k,b)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(k,\range(a,b)) \\
 & = & \take(\zero,\range(a,b)) \\
 & = & \nil \\
 & = & \range(a,\zero) \\
 & = & \range(a,\nmin(\zero,b)) \\
 & = & \range(a,\nmin(k,b))
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $a$ and $b$ for some $k$. We consider two possibilities for $b$. If $b = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\range(a,b)) \\
 & = & \take(\next(k),\range(a,\zero)) \\
 & = & \take(\next(k),\nil) \\
 & = & \nil \\
 & = & \range(a,\zero) \\
 & = & \range(a,\nmin(\next(k),\zero)) \\
 & = & \range(a,\nmin(\next(k),b))
\end{eqnarray*}$$
as needed. If $b = \next(m)$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\range(a,b)) \\
 & = & \take(\next(k),\range(a,\next(m))) \\
 & = & \take(\next(k),\cons(a,\range(\next(a),m))) \\
 & = & \cons(a,\take(k,\range(\next(a),m))) \\
 & = & \cons(a,\range(\next(a),\nmin(k,m))) \\
 & = & \range(a,\next(\nmin(k,m))) \\
 & = & \range(a,\nmin(\next(k),\next(m))) \\
 & = & \range(a,\nmin(\next(k),b))
\end{eqnarray*}$$
as needed.
</p></div>
</div>

And $\take$ is idempotent.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $k \in \nats$ and $x \in \lists{A}$, we have $$\take(k,\take(k,x)) = \take(k,x).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \take(k,\take(k,x)) \\
 & = & \take(\zero,\take(k,x)) \\
 & = & \nil \\
 & = & \take(\zero,x) \\
 & = & \take(k,x)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We now consider two possibilities. If $x = \nil$, then
$$\begin{eqnarray*}
 &   & \take(\next(k),\take(\next(k),x)) \\
 & = & \take(\next(k),\take(\next(k),\nil)) \\
 & = & \take(\next(k),\nil) \\
 & = & \take(\next(k),x)
\end{eqnarray*}$$
as needed. If $x = \cons(a,u)$, we have
$$\begin{eqnarray*}
 &   & \take(\next(k),\take(\next(k),x)) \\
 & = & \take(\next(k),\take(\next(k),\cons(a,u))) \\
 & = & \take(\next(k),\cons(a,\take(k,u))) \\
 & = & \cons(a,\take(k,\take(k,u))) \\
 & = & \cons(a,\take(k,u)) \\
 & = & \take(\next(k),\cons(a,u)) \\
 & = & \take(\next(k),x)
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Now for $\drop$. For this function, $\unfoldN$ doesn't have quite the right shape; fundamentally $\unfoldN$ "builds up" a list from the iterated images of a function, but $\drop$ needs to "tear down" a list, with it's natural number argument acting as a countdown. One of our other $\nats$ recursion operators will work for this -- we'll use bailout recursion for efficiency.

<div class="result">
<div class="defn"><p>
Let $A$ be a set. Define $\beta : \nats \times A \rightarrow \bool$ by $$\beta(m,x) = \isnil(x),$$ $\psi : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\psi(m,x) = x,$$ and $\omega : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\omega(k,x) = \tail(x).$$ We then define $\drop : \nats \times \lists{A} \rightarrow \lists{A}$ by $$\drop = \bailrec{\id}{\beta}{\psi}{\omega}.$$

In Haskell:

> drop :: (Natural n, List t) => n -> t a -> t a
> drop = bailoutRec id beta psi omega
>   where
>     beta  _ x = isNil x
>     psi   _ x = x
>     omega _ x = tail x

</p></div>
</div>

Alternatively:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $a \in A$, $x \in \lists{A}$, and $k \in \nats$, we have the following.

1. $\drop(\zero,x) = x$.
2. $\drop(k,\nil) = \nil$.
3. $\drop(\next(k),\cons(a,x)) = \drop(k,x)$.
</p></div>

<div class="proof"><p>
1. We have
$$\begin{eqnarray*}
 &   & \drop(\zero,x) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(\zero,x) \\
 & = & \id(x) \\
 & = & x
\end{eqnarray*}$$
as claimed.
2. Certainly if $k = \zero$ we have $$\drop(k,\nil) = \drop(\zero,\nil) = \nil$$ as claimed. Suppose then that $k = \next(m)$; now we have
$$\begin{eqnarray*}
 &   & \drop(k,\nil) \\
 & = & \drop(\next(m),\nil) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(\next(m),\nil) \\
 & = & \psi(m,\nil) \\
 & = & \nil
\end{eqnarray*}$$
as claimed.
3. We have
$$\begin{eqnarray*}
 &   & \drop(\next(k),\cons(a,x)) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(\next(k),\cons(a,x)) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(k,\omega(k,\cons(a,x))) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(k,\tail(\cons(a,x))) \\
 & = & \bailrec{\id}{\beta}{\psi}{\omega}(k,x) \\
 & = & \drop(k,x)
\end{eqnarray*}$$
as claimed.
</p></div>
</div>

In Haskell:

> drop' :: (Natural n, List t) => n -> t a -> t a
> drop' k x = case natShape k of
>   Zero   -> x
>   Next t -> case uncons x of
>     Left ()     -> nil
>     Right (_,u) -> drop' t u

Now $\drop$ is a $\suffix$:

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$\suffix(\drop(k,x),x) = \btrue.$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(k,x),x) \\
 & = & \suffix(\drop(\zero,x),x) \\
 & = & \suffix(x,x) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We proceed by list induction on $x$. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(\next(k),x),x) \\
 & = & \suffix(\drop(\next(k),\nil),\nil) \\
 & = & \suffix(\nil,\nil) \\
 & = & \btrue
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. By the inductive hypothesis, we have $$\suffix(\drop(k,x),x) = \btrue$$ and note also that $$\suffix(x,\cons(a,x)) = \btrue.$$ Since $\suffix$ is transitive, we have
$$\begin{eqnarray*}
 &   & \suffix(\drop(\next(k),\cons(a,x)),\cons(a,x)) \\
 & = & \suffix(\drop(k,x),\cons(a,x))
 & = & \btrue
\end{eqnarray*}$$
as needed.
</p></div>
</div>

Finally, $\take$ and $\drop$ give a kind of $\cat$-factorization.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $x \in \lists{A}$ and $k \in \nats$, we have $$x = \cat(\take(k,x),\drop(k,x)).$$
</p></div>

<div class="proof"><p>
We proceed by induction on $k$. For the base case $k = \zero$, we have
$$\begin{eqnarray*}
 &   & \cat(\take(k,x),\drop(k,x)) \\
 & = & \cat(\take(\zero,x),\drop(\zero,x)) \\
 & = & \cat(\nil,x) \\
 & = & x
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for all $x$ for some $k$. We proceed by list induction on $x$. For the base case $x = \nil$, note that
$$\begin{eqnarray*}
 &   & \cat(\take(\next(k),x),\drop(\next(k),x)) \\
 & = & \cat(\take(\next(k),\nil),\drop(\next(k),\nil)) \\
 & = & \cat(\nil,\nil) \\
 & = & \nil \\
 & = & x
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equality holds for some $x$ and let $a \in A$. Now
$$\begin{eqnarray*}
 &   & \cat(\take(\next(k),\cons(a,x)),\drop(\next(k),\cons(a,x))) \\
 & = & \cat(\cons(a,\take(k,x)),\drop(k,x)) \\
 & = & \cons(a,\cat(\take(k,x),\drop(k,x))) \\
 & = & \cons(a,x)
\end{eqnarray*}$$
as needed.
</p></div>
</div>


Testing
-------

Here are our property tests for $\take$:

> _test_take_alt :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_alt _ _ =
>   testName "take(k,x) == take'(k,x)" $
>   \k x -> eq (take k x) (take' k x)
> 
> 
> _test_take_prefix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_prefix _ _ =
>   testName "prefix(take(k,x),x) == true" $
>   \k x -> eq (prefix (take k x) x) True
> 
> 
> _test_take_length :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_length _ _ =
>   testName "length(take(k,x)) == min(k,length(x))" $
>   \k x -> eq (length (take k x)) (min k (length x))
> 
> 
> _test_take_idempotent :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_idempotent _ _ =
>   testName "take(k,(take(k,x)) == take(k,take(k,x))" $
>   \k x -> eq (take k (take k x)) (take k x)

And for $\drop$:

> _test_drop_alt :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_drop_alt _ _ =
>   testName "drop(k,x) == drop'(k,x)" $
>   \k x -> eq (drop k x) (drop' k x)
> 
> 
> _test_drop_suffix :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_drop_suffix _ _ =
>   testName "suffix(drop(k,x),x) == true" $
>   \k x -> eq (suffix (drop k x) x) True

And for both:

> _test_take_drop_cat :: (List t, Equal a, Natural n, Equal n, Equal (t a))
>   => t a -> n -> Test (n -> t a -> Bool)
> _test_take_drop_cat _ _ =
>   testName "cat(take(k,x),drop(k,x)) == x" $
>   \k x -> eq (cat (take k x) (drop k x)) x

And the suite:

> -- run all tests for take & drop
> _test_take_drop ::
>   ( TypeName a, Equal a, Show a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t
>   , TypeName n, Natural n, Show n, Arbitrary n, Equal n
>   , Equal (t a), Show (t a), Arbitrary (t a)
>   ) => t a -> n -> Int -> Int -> IO ()
> _test_take_drop t k maxSize numCases = do
>   testLabel ("take & drop: " ++ typeName t)
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_take_alt t k)
>   runTest args (_test_take_prefix t k)
>   runTest args (_test_take_length t k)
>   runTest args (_test_take_idempotent t k)
> 
>   runTest args (_test_drop_alt t k)
>   runTest args (_test_drop_suffix t k)
> 
>   runTest args (_test_take_drop_cat t k)

And ``main``:

> main_take_drop :: IO ()
> main_take_drop = do
>   _test_take_drop (nil :: ConsList Bool)  (zero :: Unary) 20 100
>   _test_take_drop (nil :: ConsList Unary) (zero :: Unary) 20 100
