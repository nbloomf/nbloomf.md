---
title: Double Bailout Fold
author: nbloomf
date: 2018-01-10
tags: arithmetic-made-difficult, literate-haskell
slug: dbfoldr
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module DoubleBailoutFold (
>   dbfoldr, _test_dbfoldr, main_dbfoldr
> ) where
> 
> import Testing
> import Booleans
> import Not
> import And
> import Or
> import Implies
> import NaturalNumbers
> import Lists
> import HeadAndTail

In this post we'll construct a hybrid of double fold and bailout fold.

:::::: theorem :::::
Let $A$ and $B$ be sets. Suppose we have maps $$\delta : B \rightarrow C,$$ $$\beta : A \times \lists{A} \times B \rightarrow \bool,$$ $$\mu : B \rightarrow B,$$ $$\psi : A \times \lists{A} \times B \rightarrow C,$$ and $$\chi : A \times B \times C \times C \rightarrow C.$$ Then there is a unique map $\Theta : \lists{A} \times B \rightarrow C$ such that $$\Theta(\nil,b) = \delta(b)$$ and
$$\Theta(\cons(a,x),b) = \left\{\begin{array}{ll}
 \psi(a,x,b) & \mathrm{if}\ \beta(a,x,b) \\
 \chi(a,x,b,\Theta(x,b),\Theta(x,\mu(b))) & \mathrm{otherwise}.
\end{array}\right.$$
We denote this $\Theta$ by $\dbfoldr{\delta}{\beta}{\mu}{\psi}{\chi}$.

::: proof ::::::::::
Define $\varepsilon : B \times \lists{A} \rightarrow C$ by $$\varepsilon(b,x) = \delta(b)$$ and $\varphi : A \times C^{B \times \lists{A}} \rightarrow C^{B \times \lists{A}}$ casewise by
$$\varphi(a,g)(b,x) = \left\{\begin{array}{ll}
 \psi(a,\tail(x),b) & \mathrm{if}\ \beta(a,\tail(x),b) \\
 \chi(a,\tail(x),b,g(b,\tail(x))),g(\mu(b),\tail(x))) & \mathrm{otherwise},
\end{array}\right.$$
and let $\Theta(x,b) = \foldr{\varepsilon}{\varphi}(x)(b,x)$. To see that $\Theta$ solves the given equations, note that
$$\begin{eqnarray*}
 &   & \Theta(\nil,b) \\
 & = & \foldr{\varepsilon}{\varphi}(\nil)(b,\nil) \\
 & = & \varepsilon(b,\nil) \\
 & = & \delta(b),
\end{eqnarray*}$$
that
$$\begin{eqnarray*}
 &   & \Theta(\cons(a,x),b) \\
 & = & \foldr{\delta}{\varphi}(\cons(a,x))(b,\cons(a,x)) \\
 & = & \varphi(a,\foldr{\delta}{\varphi}(x))(b,\cons(a,x)) \\
 & = & \left\{\begin{array}{ll}
        \psi(a,\tail(\cons(a,x)),b) & \mathrm{if}\ \beta(a,\tail(\cons(a,x)),b) \\
        \chi(a,\tail(\cons(a,x)),b,\foldr{\varepsilon}{\varphi}(x)(b,\tail(\cons(a,x))),\foldr{\varepsilon}{\varphi}(x)(\mu(b),\tail(\cons(a,x)))) & \mathrm{otherwise}
       \end{array}\right. \\
 & = & \left\{\begin{array}{ll}
        \psi(a,x,b) & \mathrm{if}\ \beta(a,x,b) \\
        \chi(a,x,b,\foldr{\varepsilon}{\varphi}(x)(b,x),\foldr{\varepsilon}{\varphi}(x)(\mu(b),x)) & \mathrm{otherwise}
       \end{array}\right. \\
 & = & \left\{\begin{array}{ll}
        \psi(a,x,b) & \mathrm{if}\ \beta(a,x,b) \\
        \chi(a,x,b,\Theta(x,b),\Theta(x,\mu(b))) & \mathrm{otherwise}
       \end{array}\right. \\
\end{eqnarray*}$$
as needed. Now suppose $\Psi : \lists{A} \times B \rightarrow C$ also satisfies the equations; we show that $\Psi = \Theta$ by list induction. For the base case $x = \nil$, we have
$$\begin{eqnarray*}
 &   & \Psi(\nil,b) \\
 & = & \delta(b) \\
 & = & \Theta(\nil,b)
\end{eqnarray*}$$
as needed. For the inductive step, suppose the equations hold for all $b$ for some $x$, and let $a \in A$. Then we have
$$\begin{eqnarray*}
 &   & \Psi(\cons(a,x),b) \\
 & = & \left\{\begin{array}{ll}
        \psi(a,x,b) & \mathrm{if}\ \beta(a,x,b) \\
        \chi(a,x,b,\Psi(x,b),\Psi(x,\mu(b))) & \mathrm{otherwise}
       \end{array}\right. \\
 & = & \left\{\begin{array}{ll}
        \psi(a,x,b) & \mathrm{if}\ \beta(a,x,b) \\
        \chi(a,x,b,\Theta(x,b),\Theta(x,\mu(b))) & \mathrm{otherwise}
       \end{array}\right. \\
 & = & \Theta(\cons(a,x),b)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::
::::::::::::::::::::


Implementation
--------------

We can implement $\dbfoldr{\ast}{\ast}{\ast}{\ast}{\ast}$ using the definition or the universal property.

> dbfoldr, dbfoldr'
>   :: (List t)
>   => (b -> c)
>   -> (a -> t a -> b -> Bool)
>   -> (b -> b)
>   -> (a -> t a -> b -> c)
>   -> (a -> t a -> b -> c -> c -> c)
>   -> t a -> b -> c
> 
> 
> dbfoldr' delta beta mu psi chi x b = foldr epsilon phi x (b,x)
>   where
>     epsilon (b,x) = delta b
> 
>     phi a g (b,x) = if beta a (tail x) b
>       then psi a (tail x) b
>       else chi a (tail x) b (g (b, tail x)) (g (mu b, tail x))
> 
> 
> -- terrible notation, or the worst notation?
> dbfoldr δ β μ ψ χ = ξ
>   where
>     ξ z b = case uncons z of
>       Left () -> δ b
>       Right (a,x) -> if β a x b
>         then ψ a x b
>         else χ a x b (ξ x b) (ξ x (μ b))

We should check that these two agree.

> _test_dbfoldr_equiv :: (List t, Equal (t a), Equal c)
>   => t a -> b -> c
>   -> Test ((b -> c) -> (a -> t a -> b -> Bool) -> (b -> b) -> (a -> t a -> b -> c) -> (a -> t a -> b -> c -> c -> c) -> t a -> b -> Bool)
> _test_dbfoldr_equiv _ _ _ =
>   testName "dbfoldr(delta,beta,mu,psi,chi)(x,b) == dbfoldr'(delta,beta,mu,psi,chi)(x,b)" $
>   \delta beta mu psi chi x b -> eq
>     (dbfoldr delta beta mu psi chi x b)
>     (dbfoldr' delta beta mu psi chi x b)


Testing
-------

Suite:

> _test_dbfoldr ::
>   ( TypeName a, Show a, Equal a, Arbitrary a, CoArbitrary a
>   , TypeName (t a), List t, Equal (t a), Arbitrary (t a), Show (t a), CoArbitrary (t a)
>   , CoArbitrary b, Arbitrary b, Show b, CoArbitrary c, Arbitrary c
>   , TypeName b, TypeName c, Equal b, Equal c
>   ) => t a -> b -> c -> Int -> Int -> IO ()
> _test_dbfoldr t b c maxSize numCases = do
>   testLabel3 "dbfoldr" t b c
> 
>   let
>     args = stdArgs
>       { maxSuccess = numCases
>       , maxSize    = maxSize
>       }
> 
>   runTest args (_test_dbfoldr_equiv t b c)

Main:

> main_dbfoldr :: IO ()
> main_dbfoldr = do
>   _test_dbfoldr (nil :: ConsList Bool)  (zero :: Unary) (zero :: Unary) 50 500
>   _test_dbfoldr (nil :: ConsList Unary) (zero :: Unary) (zero :: Unary) 50 500
>   _test_dbfoldr (nil :: ConsList Bool)  (zero :: Unary) (true :: Bool)  50 500
>   _test_dbfoldr (nil :: ConsList Unary) (zero :: Unary) (true :: Bool)  50 500
