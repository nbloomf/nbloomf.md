---
title: Composition
author: nbloomf
date: 2018-02-19
tags: arithmetic-made-difficult, literate-haskell
slug: compose
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Composition
>   ( compose2on1, compose3on1
>   , compose1on2, compose2on2
>   , compose1on3
>   , compose1on4,
>   , _test_compose, main_compose
>   ) where
> 
> import Testing
> import Functions
> import Flip

We can think of $\compose(f)(g)(x)$ as taking an outer function $f$ of one argument, and another function $g$ that massages some input $x$ before passing it on to $f$. We can express more complicated compositions of functions by stacking $\compose$ on itself in various ways -- but to avoid keeping track of too many $\compose$s it will be handy to generalize to some named operators. Say $f$ takes two arguments; a generalized compose for such a function might take two different input-massaging functions $g$ and $h$, and two inputs $x$ and $y$, and pass $g(x)$ and $h(y)$ to $f$, like $$\Theta(f)(g)(h)(x)(y) = f(g(x))(h(y)).$$ We can do exactly this with $\composeBonA$.

:::::: definition ::
[]{#def-compose2on1}
We define $$\composeBonA : (C \rightarrow D \rightarrow E) \rightarrow (A \rightarrow C) \rightarrow (B \rightarrow D) \rightarrow A \rightarrow B \rightarrow E$$ by $$\composeBonA = \flipC(\compose(\compose(\compose(\compose)))(\compose))$$

In Haskell:

> compose2on1 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
> compose2on1 = flip3 (compose (compose (compose compose)) compose)

::::::::::::::::::::

$\composeBonA$ does what we want:

:::::: theorem :::::
[]{#thm-compose2}
When the signatures of $f$, $g$, and $h$ make sense, we have $$\composeBonA(f)(g)(h)(x)(y) = f(g(x))(h(y)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \composeBonA(f)(g)(h)(x)(y) \\
 &     \href{@compose@#def-compose2on1}
   = & \flipC(\compose(\compose(\compose(\compose)))(\compose))(f)(g)(h)(x)(y) \\
 &     \href{@flip@#thm-flip3}
   = & \compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose))(\compose(f))(g)(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose)(\compose(f)(g))(x)(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(f)(g)(x))(h)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(f(g(x)))(h)(y) \\
 &     \href{@functions@#def-compose}
   = & f(g(x))(h(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose2on1
>   :: (Equal e)
>   => a -> b -> c -> d -> e
>   -> Test ((c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> Bool)
> _test_compose2on1 _ _ _ _ _ =
>   testName "compose2on1(f)(g)(h)(x)(y) == f(g(x))(h(y))" $
>   \f g h x y -> eq (compose2on1 f g h x y) (f (g x) (h y))

::::::::::::::::::::
::::::::::::::::::::

Generalizing further, $\composeConA$ acts on a function of three arguments.

:::::: definition ::
[]{#def-compose3on1}
We define
$$\begin{eqnarray*}
\composeConA
  & : & (D \rightarrow E \rightarrow F \rightarrow G) \\
  &   & \rightarrow (A \rightarrow D) \\
  &   & \rightarrow (B \rightarrow E) \\
  &   & \rightarrow (C \rightarrow F) \\
  &   & \rightarrow A \rightarrow B \rightarrow C \rightarrow G
\end{eqnarray*}$$
by $$\composeConA = \flipD(\flipE(\flipC(\compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose)))))$$

In Haskell:

> compose3on1
>   :: (d -> e -> f -> g)
>   -> (a -> d)
>   -> (b -> e)
>   -> (c -> f)
>   -> a -> b -> c -> g
> 
> compose3on1 =
>   flip4 (flip5 (flip3 (
>     compose
>       (compose (compose (compose (compose compose))))
>       (compose
>         (compose (compose compose))
>         (compose))
>   )))

::::::::::::::::::::

And $\composeConA$ does what we want.

:::::: theorem :::::
[]{#thm-compose3on1}
Whenever the signatures of $f$, $g$, $h$, and $k$ make sense, we have $$\compose3(f)(g)(h)(k)(x)(y)(z) = f(g(x))(h(y))(k(z)).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \composeConA(f)(g)(h)(k)(x)(y)(z) \\
 &     \href{@compose@#def-compose3on1}
   = & \flipD(\flipE(\flipC(\compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose)))))(f)(g)(h)(k)(x)(y)(z) \\
 &     \href{@flip@#thm-flip4}
   = & \flipE(\flipC(\compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose))))(f)(g)(h)(x)(k)(y)(z) \\
 &     \href{@flip@#thm-flip5}
   = & \flipC(\compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose)))(f)(g)(h)(x)(y)(k)(z) \\
 &     \href{@flip@#thm-flip3}
   = & \compose(\compose(\compose(\compose(\compose(\compose)))))(\compose(\compose(\compose(\compose)))(\compose))(f)(g)(x)(h)(y)(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose(\compose(\compose))))(\compose(\compose(\compose(\compose)))(\compose)(f))(g)(x)(h)(y)(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose(\compose)))(\compose(\compose(\compose(\compose)))(\compose)(f)(g))(x)(h)(y)(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose))(\compose(\compose(\compose(\compose)))(\compose)(f)(g)(x))(h)(y)(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose)(\compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h))(y)(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h)(y))(k)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h)(y)(k(z)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose))(\compose(f))(g)(x)(h)(y)(k(z)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose)(\compose(f)(g))(x)(h)(y)(k(z)) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(f)(g)(x))(h)(y)(k(z)) \\
 &     \href{@functions@#def-compose}
   = & \compose(f)(g)(x)(h(y))(k(z)) \\
 &     \href{@functions@#def-compose}
   = & f(g(x))(h(y))(k(z))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose3on1
>   :: (Equal g)
>   => a -> b -> c -> d -> e -> f -> g
>   -> Test ((d -> e -> f -> g) -> (a -> d) -> (b -> e) -> (c -> f) -> a -> b -> c -> Bool)
> _test_compose3on1 _ _ _ _ _ _ _ =
>   testName "compose3on1(f)(g)(h)(k)(x)(y)(z) == f(g(x))(h(y))(k(z))" $
>   \f g h k x y z -> eq (compose3on1 f g h k x y z) (f (g x) (h y) (k z))

::::::::::::::::::::
::::::::::::::::::::

A really good question to ask at this point is, "where on earth did those definitions for $\composeBonA$ and $\composeConA$ come from?" It's almost certainly not obvious how we could write such a thing down without already knowing some trick. And there is a trick -- it turns out we can _calculate_ these definitions, and others, using the known properties of our function operators. Take $\composeBonA$ for example. Say we're setting out to find a definition for the map $\Theta(f)(g)(h)(x)(y) = f(g(x))(h(y))$. First off, I know from experience that (1) with $\compose$, we can move function arguments in and out of parentheses as long as they're in the right order, and (2) putting the arguments of a function in any given order is easy with $\flip$ and friends. So we might as well start out looking for $\Theta$ such that $$\Theta(f)(g)(x)(h)(y) = f(g(x))(h(y)),$$ since we can apply an appropriate sequence of $\flip$s to $\Theta$ at the end.

Now, working backwards, start with $$f(g(x))(h(y)).$$ Note that this fits the pattern of a $\compose$, where the outer function is $f(g(x))$, and the inner function is $h$. So this expression is equivalent to $$\compose(f(g(x)))(h)(y).$$ We've peeled off the last two arguments of $\Theta$ already. We'd like to peel off the next argument from the right; in this case, $x$. Imagine that the $x$ argument is trapped inside two extra sets of parentheses. And the tool for eliminating parentheses is $\compose$. Indeed, we can write $f(g(x)) = \compose(f)(g)(x)$, and now $x$ is "lifted up" by one level. So our expression is now equivalent to $$\compose(\compose(f)(g)(x))(h)(y).$$ We can play this game again; $x$ is still trapped, and is the argument of a composition where the outer function is $\compose$ and the inner function is $\compose(f)(g)$. So our expression is equivalent to $$\compose(\compose)(\compose(f)(g))(x)(h)(y).$$ We can see the trick now; $g$ is trapped, and another $\compose$ gives $$\compose(\compose(\compose))(\compose(f))(g)(x)(h)(y).$$ Now $f$ is trapped, but another $\compose$ gives $$\compose(\compose(\compose(\compose)))(\compose)(f)(g)(x)(h)(y).$$ So we have $$\Theta = \compose(\compose(\compose(\compose)))(\compose),$$ and applying a $\flipC$ to this map gives the $\compose2$ we defined above.

A similar trick applies when we want to use some input more than once; this time we assume that an appropriate $\clone$ has been applied.

Two more generalizations of $\compose$ will also be handy.

:::::: definition ::
[]{#def-compose1on2}
We define $$\composeAonB : (C \rightarrow D) \rightarrow (A \rightarrow B \rightarrow C) \rightarrow A \rightarrow B \rightarrow D$$ by $$\composeAonB = \compose(\compose)(\compose)$$

In Haskell:

> compose1on2 :: (c -> d) -> (a -> b -> c) -> a -> b -> d
> compose1on2 = compose compose compose

::::::::::::::::::::

And $\composeAonB$ behaves like so:

:::::: theorem :::::
[]{#thm-compose1on2}
We have $$\composeAonB(f)(g)(x)(y) = f(g(x)(y)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \composeAonB(f)(g)(x)(y) \\
 &     \href{@compose@#def-compose1on2}
   = & \compose(\compose)(\compose)(f)(g)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(f))(g)(x)(y) \\
 &     \href{@functions@#def-compose}
   = & \compose(f)(g(x))(y) \\
 &     \href{@functions@#def-compose}
   = & f(g(x)(y))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose1on2
>   :: (Equal d)
>   => a -> b -> c -> d
>   -> Test ((c -> d) -> (a -> b -> c) -> a -> b -> Bool)
> _test_compose1on2 _ _ _ _ =
>   testName "compose1on2(f)(g)(x)(y) == f(g(x)(y))" $
>   \f g x y -> eq (compose1on2 f g x y) (f (g x y))

::::::::::::::::::::
::::::::::::::::::::

Now:

:::::: definition ::
[]{#def-compose1on3}
We define $$\composeAonC : (D \rightarrow E) \rightarrow (A \rightarrow B \rightarrow C \rightarrow D) \rightarrow A \rightarrow B \rightarrow C \rightarrow E$$ by $$\composeAonC = \compose(\compose)(\composeAonB)$$

In Haskell:

> compose1on3 :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
> compose1on3 = compose compose compose1on2

::::::::::::::::::::

And $\composeAonC$ behaves like so:

:::::: theorem :::::
[]{#thm-compose1on3}
We have $$\composeAonC(f)(g)(x)(y)(z) = f(g(x)(y)(z)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \composeAonC(f)(g)(x)(y)(z) \\
 &     \href{@compose@#def-compose1on3}
   = & \compose(\compose)(\composeAonB)(f)(g)(x)(y)(z) \\
 &     \href{@functions@#def-compose}
   = & \compose(\composeAonB(f))(g)(x)(y)(z) \\
 &     \href{@functions@#def-compose}
   = & \composeAonB(f)(g(x))(y)(z) \\
 &     \href{@compose@#thm-compose1on2}
   = & f(g(x)(y)(z))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose1on3
>   :: (Equal e)
>   => a -> b -> c -> d -> e
>   -> Test ((d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> Bool)
> _test_compose1on3 _ _ _ _ _ =
>   testName "compose1on3(f)(g)(x)(y)(z) == f(g(x)(y)(z))" $
>   \f g x y z -> eq (compose1on3 f g x y z) (f (g x y z))

::::::::::::::::::::
::::::::::::::::::::

Now:

:::::: definition ::
[]{#def-compose1on4}
We define $$\composeAonD : (E \rightarrow F) \rightarrow (A \rightarrow B \rightarrow C \rightarrow D \rightarrow E) \rightarrow A \rightarrow B \rightarrow C \rightarrow D \rightarrow F$$ by $$\composeAonD = \compose(\compose)(\composeAonC)$$

In Haskell:

> compose1on4 :: (e -> f) -> (a -> b -> c -> d -> e) -> a -> b -> c -> d -> f
> compose1on4 = compose compose compose1on3

::::::::::::::::::::

And $\composeAonD$ behaves like so:

:::::: theorem :::::
[]{#thm-compose1on4}
We have $$\composeAonD(f)(g)(x)(y)(z)(w) = f(g(x)(y)(z)(w)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \composeAonD(f)(g)(x)(y)(z)(w) \\
 &     \href{@compose@#def-compose1on4}
   = & \compose(\compose)(\composeAonC)(f)(g)(x)(y)(z)(w) \\
 &     \href{@functions@#def-compose}
   = & \compose(\composeAonC(f))(g)(x)(y)(z)(w) \\
 &     \href{@functions@#def-compose}
   = & \composeAonC(f)(g(x))(y)(z)(w) \\
 &     \href{@compose@#thm-compose1on3}
   = & f(g(x)(y)(z)(w))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose1on4
>   :: (Equal f)
>   => a -> b -> c -> d -> e -> f
>   -> Test ((e -> f) -> (a -> b -> c -> d -> e) -> a -> b -> c -> d -> Bool)
> _test_compose1on4 _ _ _ _ _ _ =
>   testName "compose1on4(f)(g)(x)(y)(z)(w) == f(g(x)(y)(z)(w))" $
>   \f g x y z w -> eq (compose1on4 f g x y z w) (f (g x y z w))

::::::::::::::::::::
::::::::::::::::::::

Now:

:::::: definition ::
[]{#def-compose2on2}
We define
$$\begin{eqnarray*}
\composeBonB
  & : & (E \rightarrow F \rightarrow G) \\
  &   & \rightarrow (A \rightarrow B \rightarrow E) \\
  &   & \rightarrow (C \rightarrow D \rightarrow F) \\
  &   & \rightarrow A \rightarrow B \rightarrow C \rightarrow D \rightarrow G
\end{eqnarray*}$$
by $$\composeBonB = $$

In Haskell:

> compose2on2 :: (e -> f -> g) -> (a -> b -> e) -> (c -> d -> f) -> a -> b -> c -> d -> g
> compose2on2 = flip5 (compose compose2on1 compose2on1)

::::::::::::::::::::

And $\composeBonB$ behaves like so:

:::::: theorem :::::
[]{#thm-compose2on2}
We have $$\composeBonB(f)(g)(h)(x)(y)(z)(w) = f(g(x)(y))(h(z)(w)).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \composeBonB(f)(g)(h)(x)(y)(z)(w) \\
 &     \href{@compose@#def-compose2on2}
   = & \flipE(\compose(\composeBonA)(\composeBonA))(f)(g)(h)(x)(y)(z)(w) \\
 &     \href{@flip@#thm-flip5}
   = & \compose(\composeBonA)(\composeBonA)(f)(g)(h)(x)(z)(y)(w) \\
 &     \href{@functions@#def-compose}
   = & \composeBonA(\composeBonA(f))(g)(h)(x)(z)(y)(w) \\
 &     \href{@compose@#thm-compose2on1}
   = & \composeBonA(f)(g(x))(h(z))(y)(w) \\
 &     \href{@compose@#thm-compose2on1}
   = & f(g(x)(y))(h(z)(w))
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_compose2on2
>   :: (Equal g)
>   => a -> b -> c -> d -> e -> f -> g
>   -> Test ((e -> f -> g) -> (a -> b -> e) -> (c -> d -> f) -> a -> b -> c -> d -> Bool)
> _test_compose2on2 _ _ _ _ _ _ _ =
>   testName "compose2on2(f)(g)(h)(x)(y)(z)(w) == f(g(x)(y))(h(z)(w))" $
>   \f g h x y z w -> eq (compose2on2 f g h x y z w) (f (g x y) (h z w))

::::::::::::::::::::
::::::::::::::::::::


Testing
-------

Suite:

> _test_compose ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a, TypeName a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b, TypeName b
>   , Equal c, Show c, Arbitrary c, CoArbitrary c, TypeName c
>   , Equal d, Show d, Arbitrary d, CoArbitrary d, TypeName d
>   , Equal e, Show e, Arbitrary e, CoArbitrary e, TypeName e
>   , Equal f, Show f, Arbitrary f, CoArbitrary f, TypeName f
>   , Equal g, Show g, Arbitrary g, CoArbitrary g, TypeName g
>   ) => Int -> Int -> a -> b -> c -> d -> e -> f -> g -> IO ()
> 
> _test_compose size cases a b c d e f g = do
>   testLabel0 "compose"
>   let args = testArgs size cases
> 
>   runTest args (_test_compose1on2 a b c d)
>   runTest args (_test_compose1on3 a b c d e)
>   runTest args (_test_compose1on4 a b c d e f)
>   runTest args (_test_compose2on1 a b c d e)
>   runTest args (_test_compose2on2 a b c d e f g)
>   runTest args (_test_compose3on1 a b c d e f g)

Main:

> main_compose :: IO ()
> main_compose = do
>   _test_compose 1 1 () () () () () () ()
