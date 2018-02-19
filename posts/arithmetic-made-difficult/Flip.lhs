---
title: Flip
author: nbloomf
date: 2018-02-17
tags: arithmetic-made-difficult, literate-haskell
slug: flip
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Flip (
>   flip, flip2, flip3, flip4, flip5, _test_flip, main_flip
> ) where
> 
> import Testing
> import Functions

It turns out that equational proofs are much simpler to state and verify if we define new functions in the so-called _pointfree_ style. A pointfree function definition is one that does not refer to its arguments explicitly; for example, suppose we have two functions $f : A \rightarrow B$ and $g : B \rightarrow C$, and have defined a new function $h : A \rightarrow C$ by $$h(x) = g(f(x)).$$ Of course this definition is equivalent to $$h(x) = \compose(g)(f)(x).$$ But now the rightmost argument, $x$, can be omitted, leaving $$h = \compose(g)(f).$$ This final statement is written in the pointfree style. We'll see later that definitions will cooperate better with equational reasoning if they are in pointfree form. To make this work, we'll need a stable of operators for manipulating functions, like $\compose$ in the above example. In all cases the goal will be to move function arguments around; for instance, $\compose$ lets us move a rightmost argument "up" one level of parentheses.

In this post we'll define a family of operators that rearrange the arguments of a multi-argument function. The first example is $\flip$, which flips the arguments of a two-argument function.

:::::: definition ::
[]{#def-flip}
Let $A$, $B$, and $C$ be sets. Given $f : A \rightarrow B \rightarrow C$, we define $\flip(f) : B \rightarrow A \rightarrow C$ by $$\flip(f)(b)(a) = f(a)(b).$$

In Haskell:

> flip :: (a -> b -> c) -> b -> a -> c
> flip f b a = f a b

::::::::::::::::::::

$\flip$ is an involution.

:::::: theorem :::::
[]{#thm-flip-involution}
Let $A$, $B$, and $C$ be sets. For all $f : A \rightarrow B \rightarrow C$, we have $$\flip(\flip(f)) = f.$$

::: proof ::::::::::
Let $a \in A$ and $b \in B$. Then we have
$$\begin{eqnarray*}
 &   & \flip(\flip(f))(a)(b) \\
 &     \href{@flip@#def-flip}
   = & \flip(f)(b)(a) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)
\end{eqnarray*}$$
as needed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip_involution
>   :: (Equal c)
>   => a -> b -> c
>   -> Test ((a -> b -> c) -> a -> b -> Bool)
> _test_flip_involution _ _ _ =
>   testName "flip(flip(f)) == f" $
>   \f a b -> eq (flip (flip f) a b) (f a b)

::::::::::::::::::::
::::::::::::::::::::

Ostensibly, $\flip$ acts on functions of two arguments. But since the return type of such a function can be another function, a better way to think of $\flip$ is that it flips the _first two_ arguments of a multi-argument function.

:::::: theorem :::::
[]{#thm-flip-three}
Let $f : A \rightarrow B \rightarrow C \rightarrow D$. Then we have $$\flip(f)(b)(a)(c)(d) = f(a)(b)(c)(d).$$

::: proof ::::::::::
Note that
$$\begin{eqnarray*}
 &   & \flip(f)(b)(a)(c) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)(c)
\end{eqnarray*}$$
::::::::::::::::::::

::: test :::::::::::

> _test_flip_3
>   :: (Equal d)
>   => a -> b -> c -> d
>   -> Test ((a -> b -> c -> d) -> a -> b -> c -> Bool)
> _test_flip_3 _ _ _ _ =
>   testName "flip(f)(a)(b)(c) == f(b)(a)(c)" $
>   \f a b c -> eq (flip f b a c) (f a b c)

::::::::::::::::::::
::::::::::::::::::::

Okay- what about more general permutations of function arguments? Let's start with flipping the second and third.

:::::: definition ::
[]{#def-flip2}
Let $A$, $B$, $C$, and $D$ be sets. Given $f : A \rightarrow B \rightarrow C \rightarrow D$, we define $\flipB(f) : A \rightarrow C \rightarrow B \rightarrow D$ by $$\flipB = \compose(\flip).$$

In Haskell:

> flip2 :: (a -> b -> c -> d) -> a -> c -> b -> d
> flip2 = compose flip

::::::::::::::::::::

Now $\flipB$ permutes function arguments.

:::::: theorem :::::
[]{#thm-flip2}
Let $f : A \rightarrow B \rightarrow C \rightarrow D$. Then $$\flipB(f)(a)(c)(b) = f(a)(b)(c).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \flipB(f)(a)(c)(b) \\
 &     \href{@flip@#def-flip2}
   = & \compose(\flip)(f)(a)(c)(b) \\
 &     \href{@functions@#def-compose}
   = & \flip(f(a))(c)(b) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)(c)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip2
>   :: (Equal d)
>   => a -> b -> c -> d
>   -> Test ((a -> b -> c -> d) -> a -> b -> c -> Bool)
> _test_flip2 _ _ _ _ =
>   testName "flip2(f)(a)(b)(c) == f(a)(c)(b)" $
>   \f a b c -> eq (flip2 f a c b) (f a b c)

::::::::::::::::::::
::::::::::::::::::::

And we can flip the third and fourth arguments.

:::::: definition ::
[]{#def-flip3}
Let $A$, $B$, $C$, $D$, and $E$ be sets. We define $$\flipC : (A \rightarrow B \rightarrow C \rightarrow D \rightarrow E) \rightarrow A \rightarrow B \rightarrow D \rightarrow C \rightarrow E$$ by $$\flipC = \compose(\compose(\flip)).$$

In Haskell:

> flip3 :: (a -> b -> c -> d -> e) -> a -> b -> d -> c -> e
> flip3 = compose (compose flip)

::::::::::::::::::::

$\flipC$ does the thing:

:::::: theorem :::::
[]{#thm-flip3}
Let $f : A \rightarrow B \rightarrow C \rightarrow D \rightarrow E$. Then $$\flipC(f)(a)(b)(d)(c) = f(a)(b)(c)(d).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \flipC(f)(a)(b)(d)(c) \\
 &     \href{@flip@#def-flip3}
   = & \compose(\compose(\flip))(f)(a)(b)(d)(c) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(f(a))(b)(d)(c) \\
 &     \href{@functions@#def-compose}
   = & \flip(f(a)(b))(d)(c) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)(c)(d)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip3
>   :: (Equal e)
>   => a -> b -> c -> d -> e
>   -> Test ((a -> b -> c -> d -> e) -> a -> b -> c -> d -> Bool)
> _test_flip3 _ _ _ _ _ =
>   testName "flip3(f)(a)(b)(c)(d) == f(a)(b)(d)(c)" $
>   \f a b c d -> eq (flip3 f a b d c) (f a b c d)

::::::::::::::::::::
::::::::::::::::::::

We'll look at two more examples, to see the pattern emerging.

:::::: definition ::
[]{#def-flip4}
We define $\flipD : (A \rightarrow B \rightarrow C \rightarrow D \rightarrow E \rightarrow F) \rightarrow A \rightarrow B \rightarrow C \rightarrow E \rightarrow D \rightarrow F$ by $$\flipD = \compose(\compose(\compose(\flip))).$$

In Haskell:

> flip4
>   :: (a -> b -> c -> d -> e -> f)
>   -> a -> b -> c -> e -> d -> f
> 
> flip4 =
>   compose (compose (compose flip))

::::::::::::::::::::

And:

:::::: theorem :::::
[]{#thm-flip4}
Let $f : A \rightarrow B \rightarrow C \rightarrow D \rightarrow E \rightarrow F$. Then $$\flipD(f)(a)(b)(c)(e)(d) = f(a)(b)(c)(d)(e).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \flipD(f)(a)(b)(c)(e)(d) \\
 &     \href{@flip@#def-flip4}
   = & \compose(\compose(\compose(\flip)))(f)(a)(b)(c)(e)(d) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\flip))(f(a))(b)(c)(e)(d) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(f(a)(b))(c)(e)(d) \\
 &     \href{@functions@#def-compose}
   = & \flip(f(a)(b)(c))(e)(d) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)(c)(d)(e)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip4 :: (Equal f)
>   => a -> b -> c -> d -> e -> f
>   -> Test ((a -> b -> c -> d -> e -> f) -> a -> b -> c -> d -> e -> Bool)
> _test_flip4 _ _ _ _ _ _ =
>   testName "flip4(f)(a)(b)(c)(d)(e) == f(a)(b)(c)(e)(d)" $
>   \f a b c d e -> eq (flip4 f a b c e d) (f a b c d e)

::::::::::::::::::::
::::::::::::::::::::

One more.

:::::: definition ::
[]{#def-flip5}
We define $$\flipE : (A \rightarrow B \rightarrow C \rightarrow D \rightarrow E \rightarrow F \rightarrow G) \rightarrow A \rightarrow B \rightarrow C \rightarrow D \rightarrow F \rightarrow E \rightarrow G$$ by $$\flipE = \compose(\compose(\compose(\compose(\flip)))).$$

In Haskell:

> flip5
>   :: (a -> b -> c -> d -> e -> f -> g)
>   -> a -> b -> c -> d -> f -> e -> g
> 
> flip5 = compose (compose (compose (compose flip)))

::::::::::::::::::::

And:

:::::: theorem :::::
[]{#thm-flip5}
Let $f : A \rightarrow B \rightarrow C \rightarrow D \rightarrow E \rightarrow F \rightarrow G$. Then $$\flipE(f)(a)(b)(c)(d)(f)(e) = f(a)(b)(c)(d)(e)(f).$$

::: proof ::::::::::
We have
$$\begin{eqnarray*}
 &   & \flipE(f)(a)(b)(c)(d)(f)(e) \\
 &     \href{@flip@#def-flip5}
   = & \compose(\compose(\compose(\compose(\flip))))(f)(a)(b)(c)(d)(f)(e) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\compose(\flip)))(f(a))(b)(c)(d)(f)(e) \\
 &     \href{@functions@#def-compose}
   = & \compose(\compose(\flip))(f(a)(b))(c)(d)(f)(e) \\
 &     \href{@functions@#def-compose}
   = & \compose(\flip)(f(a)(b)(c))(d)(f)(e) \\
 &     \href{@functions@#def-compose}
   = & \flip(f(a)(b)(c)(d))(f)(e) \\
 &     \href{@flip@#def-flip}
   = & f(a)(b)(c)(d)(e)(f)
\end{eqnarray*}$$
as claimed.
::::::::::::::::::::

::: test :::::::::::

> _test_flip5
>   :: (Equal g)
>   => a -> b -> c -> d -> e -> f -> g
>   -> Test ((a -> b -> c -> d -> e -> f -> g)
>       -> a -> b -> c -> d -> e -> f -> Bool)
> _test_flip5 _ _ _ _ _ _ _ =
>   testName "flip5(f)(a)(b)(c)(d)(e)(f) == f(a)(b)(c)(d)(f)(e)" $
>   \w a b c d e f -> eq (flip5 w a b c d f e) (w a b c d e f)

::::::::::::::::::::
::::::::::::::::::::

Well that's neat. This pattern continues, and we can define an operator that flips the $n$th and $(n+1)$th argument, for any $n$, using just $\compose$ and $\flip$. And it turns out that this is enough to generate arbitrary permutations of the arguments of any function, by composing the flip operators in the right order. We won't prove this in full generality here (not yet, anyway).


Testing
-------

Suite:

> _test_flip ::
>   ( Equal a, Show a, Arbitrary a, CoArbitrary a, TypeName a
>   , Equal b, Show b, Arbitrary b, CoArbitrary b, TypeName b
>   , Equal c, Show c, Arbitrary c, CoArbitrary c, TypeName c
>   , Equal d, Show d, Arbitrary d, CoArbitrary d, TypeName d
>   , Equal e, Show e, Arbitrary e, CoArbitrary e, TypeName e
>   , Equal f, Show f, Arbitrary f, CoArbitrary f, TypeName f
>   , Equal g, Show g, Arbitrary g, CoArbitrary g, TypeName g
>   ) => Int -> Int -> a -> b -> c -> d -> e -> f -> g -> IO ()
> 
> _test_flip size cases a b c d e f g = do
>   testLabel0 "flip"
>   let args = testArgs size cases
> 
>   runTest args (_test_flip_involution a b c)
>   runTest args (_test_flip_3 a b c d)
>   runTest args (_test_flip2 a b c d)
>   runTest args (_test_flip3 a b c d e)
>   runTest args (_test_flip4 a b c d e f)
>   runTest args (_test_flip5 a b c d e f g)

Main:

> main_flip :: IO ()
> main_flip = do
>   _test_flip 1 1 () () () () () () ()
