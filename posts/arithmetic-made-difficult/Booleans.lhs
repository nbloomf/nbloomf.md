---
title: Booleans
author: nbloomf
date: 2014-04-01
tags: arithmetic-made-difficult, literate-haskell
slug: booleans
---

> {-# LANGUAGE NoImplicitPrelude #-}
> module Booleans
>   ( Boolean, true, false, ifThenElse
>   , Equal, eq
>   , _test_boolean, main_boolean
>   ) where
> 
> import Testing

Before we think about numbers or writing programs, let's start by nailing down some important ideas about truth values. In math there can be a kind of other-worldness about True and False, since they live in the "metalanguage" of mathematical logic rather than the "object language" of whatever we are studying. But it will turn out to be useful to algebraify the truth values themselves.

We're going to characterize the boolean values true and false in a roundabout way. This might look strange at first, but there's a good reason for it. First, we define a kind of algebra.

:::: definition ::::
A *doubly-pointed set* is a set $A$ with two (not necessarily distinct) distinguished elements $a_t, a_f \in A$. If $A$ and $B$ are doubly-pointed sets with distinguished elements $a_t, a_f \in A$ and $b_t, b_f \in B$, a map $\theta : A \rightarrow B$ is called a *doubly-pointed homomorphism* if $\theta(a_t) = b_t$ and $\theta(a_f) = b_f$.
::::::::::::::::::::

As algebras go, doubly-pointed sets are almost as weak as they come. We can see shades of the boolean values there -- "true" and "false" can be thought of as distinguished elements  in a doubly-pointed set. And indeed we'll do that. But the booleans are not just any set; they are the smallest such set in a precise sense.

:::: definition ::::
There is a special doubly-pointed set, denoted $\bool$, with distinguished elements $\btrue$ and $\bfalse$, with the property that if $A$ is a doubly-pointed set with distinguished elements $a_t, a_f$, then there is a *unique* doubly-pointed homomorphism $\Theta : \bool \rightarrow A$. We denote this $\Theta$ by $$\Theta(p) = \bif{p}{a_t}{a_f}.$$ To be clear, we have $$\bif{\btrue}{a_t}{a_f} = a_t$$ and $$\bif{\bfalse}{a_t}{a_f} = a_f.$$
::::::::::::::::::::

What makes *the* booleans special is this unique map, which looks suspiciously like the traditional "if-then-else" construct, because that's exactly what it is.

I'm referring to "the" booleans as if they are uniquely determined, but of course they aren't -- any other doubly-pointed set that also maps uniquely to any other is indistinguishable from $\bool$. For this reason we'll wrap up the important information about $\bool$ in a type class, rather than a single type.

> class Boolean b where
>   true :: b
>   false :: b
> 
>   ifThenElse :: b -> a -> a -> a

Of course the Haskell ``Bool`` type is an instance.

> instance Boolean Bool where
>   true = True
>   false = False
> 
>   ifThenElse p x y = if p then x else y

We can test this instance. Remember the defining property of $\bif{\ast}{\ast}{\ast}$ is that it preserves distinguished points.

> _test_if_true :: (Boolean b, Equal a)
>   => b -> a -> Test (a -> a -> Bool)
> _test_if_true p _ =
>   testName "if(true,a,b) == a" $
>   \x y -> eq (ifThenElse (true `withTypeOf` p) x y) x
> 
> 
> _test_if_false :: (Boolean b, Equal a)
>   => b -> a -> Test (a -> a -> Bool)
> _test_if_false p _ =
>   testName "if(false,a,b) == a" $
>   \x y -> eq (ifThenElse (false `withTypeOf` p) x y) y

There are many other instances which essentially differ only by the labels of $\btrue$ and $\bfalse$, and depending on the context, a different concrete instance might make more sense. We could call the distinguished elements of $\bool$ "Yes/No", "Present/Absent", or something else, and the essence of booleanness would not change.


(@@@)


Now $\bif{\ast}{\ast}{\ast}$ also satisfies some useful properties.

If interacts with function application:

<div class="result">
<div class="thm"><p><a name="thm-iffunc" />
Let $A$ and $B$ be sets with $f : A \rightarrow B$ a map. For all $p \in \bool$ and $u,v \in A$, we have $$f(\bif{p}{u}{v}) = \bif{p}{f(u)}{f(v)}.$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\btrue}{u}{v}) \\
 & = & f(u) \\
 & = & \bif{\btrue}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{u}{v}) \\
 & = & f(\bif{\bfalse}{u}{v}) \\
 & = & f(v) \\
 & = & \bif{\bfalse}{f(u)}{f(v)} \\
 & = & \bif{p}{f(u)}{f(v)}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_func :: (Equal a)
>   => a -> Test ((a -> a) -> Bool -> a -> a -> Bool)
> _test_if_func _ =
>   testName "f(if(p,a,b)) == if(p,f(a),f(b))" $
>   \f p a b -> eq (f (ifThenElse p a b)) (ifThenElse p (f a) (f b))

</p></div>
</div>

Nested $\bif{\ast}{\ast}{\ast}$s commute (sort of).

<div class="result">
<div class="thm"><p><a name="thm-ifnest" />
Let $A$ be a set with $p,q \in \bool$ and $a,b,c,d \in A$. Then we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}}.
\end{eqnarray*}$$
</p></div>

<div class="proof"><p>
We have four possibilities for $(p,q)$. If $p = \btrue$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\btrue}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{a}{b} \\
 & = & a \\
 & = & \bif{\btrue}{a}{c} \\
 & = & \bif{\btrue}{\bif{\btrue}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \btrue$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{a}{b} \\
 & = & b \\
 & = & \bif{\btrue}{b}{d} \\
 & = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\btrue}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \btrue$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\btrue}{c}{d}} \\
 & = & \bif{\btrue}{c}{d} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{\btrue}{\bif{\bfalse}{a}{c}}{\bif{p}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed. If $p = \bfalse$ and $q = \bfalse$,
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{q}{a}{b}}{\bif{q}{c}{d}} \\
 & = & \bif{\bfalse}{\bif{q}{a}{b}}{\bif{\bfalse}{c}{d}} \\
 & = & \bif{\bfalse}{c}{d} \\
 & = & d \\
 & = & \bif{\bfalse}{b}{d} \\
 & = & \bif{\bfalse}{\bif{p}{a}{c}}{\bif{\bfalse}{b}{d}} \\
 & = & \bif{q}{\bif{p}{a}{c}}{\bif{p}{b}{d}} \\
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_nest :: (Equal a)
>   => a -> Test (Bool -> Bool -> a -> a -> a -> a -> Bool)
> _test_if_nest _ =
>   testName "if(p,if(q,a,b),if(q,c,d)) == if(q,if(p,a,c),if(p,b,d))" $
>   \p q a b c d ->
>     eq
>       (ifThenElse p (ifThenElse q a b) (ifThenElse q c d))
>       (ifThenElse q (ifThenElse p a c) (ifThenElse p b d))

</p></div>
</div>

Nested ifs on the same boolean can be pruned.

<div class="result">
<div class="thm"><p><a name="thm-ifprune" />
Let $A$ be a set with $p \in \bool$ and $a,b,c \in A$. We have the following.

1. $\bif{p}{\bif{p}{a}{b}}{c} = \bif{p}{a}{c}$
2. $\bif{p}{a}{\bif{p}{b}{c}} = \bif{p}{a}{c}$
</p></div>

<div class="proof"><p>
1. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{p}{\bif{\btrue}{a}{b}}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed. If $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{\bif{p}{a}{b}}{c} \\
 & = & \bif{\bfalse}{\bif{\bfalse}{a}{b}}{c} \\
 & = & c \\
 & = & \bif{\bfalse}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as needed.
2. If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{\btrue}{a}{\bif{p}{b}{c}} \\
 & = & a \\
 & = & \bif{\btrue}{a}{c} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed, and if $p = \bfalse$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{p}{b}{c}} \\
 & = & \bif{p}{a}{\bif{\bfalse}{b}{c}} \\
 & = & \bif{p}{a}{c}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_prune_left :: (Equal a)
>   => a -> Test (Bool -> a -> a -> a -> Bool)
> _test_if_prune_left _ =
>   testName "if(p,if(p,a,b),c) == if(p,a,c)" $
>   \p a b c -> eq (ifThenElse p (ifThenElse p a b) c) (ifThenElse p a c)
> 
> 
> _test_if_prune_right :: (Equal a)
>   => a -> Test (Bool -> a -> a -> a -> Bool)
> _test_if_prune_right _ =
>   testName "if(p,a,if(p,b,c)) == if(p,a,c)" $
>   \p a b c -> eq (ifThenElse p a (ifThenElse p b c)) (ifThenElse p a c)

</p></div>
</div>

$\bif{\ast}{\ast}{\ast}$ is sort of commutative.

<div class="result">
<div class="thm"><p>
Let $A$ be a set. For all $p,q \in \bool$ and $a,b \in A$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & \bif{q}{a}{\bif{p}{a}{b}}.
\end{eqnarray*}$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & a \\
 & = & \bif{q}{a}{a} \\
 & = & \bif{q}{a}{\bif{p}{a}{c}}
\end{eqnarray*}$$
as claimed. Likewise, the equality holds if $q = \btrue$. Suppose then that $p = q = \bfalse$; now
$$\begin{eqnarray*}
 &   & \bif{p}{a}{\bif{q}{a}{b}} \\
 & = & \bif{q}{a}{b} \\
 & = & b \\
 & = & \bif{p}{a}{b} \\
 & = & \bif{q}{a}{\bif{p}{a}{b}}
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_commute_left :: (Equal a)
>   => a -> Test (Bool -> Bool -> a -> a -> Bool)
> _test_if_commute_left _ =
>   testName "if(p,a,if(q,a,b)) == if(q,a,if(p,a,b))" $
>   \p q a b -> eq
>     (ifThenElse p a (ifThenElse q a b))
>     (ifThenElse q a (ifThenElse p a b))

</p></div>
</div>

$\bif{\ast}{\ast}{\ast}$ interacts with functions of two arguments.

<div class="result">
<div class="thm"><p>
We have $$f(\bif{p}{a}{c},\bif{p}{b}{d}) = \bif{p}{f(a,b)}{f(c,d)}.$$
</p></div>

<div class="proof"><p>
If $p = \btrue$, we have
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 & = & f(a,b)
\end{eqnarray*}$$
and if $p = \bfalse,
$$\begin{eqnarray*}
 &   & f(\bif{p}{a}{c},\bif{p}{b}{d}) \\
 & = & f(c,d)
\end{eqnarray*}$$
as claimed.
</p></div>

<div class="test"><p>

> _test_if_two_args :: (Equal a)
>   => a -> Test ((a -> a -> a) -> Bool -> a -> a -> a -> a -> Bool)
> _test_if_two_args _ =
>   testName "f(if(p,a,c),if(p,b,x)) == if(p,f(a,b),f(c,d))" $
>   \f p a b c d -> eq
>     (f (if p then a else c) (if p then b else d))
>     (if p then f a b else f c d)

</p></div>
</div>


Equality
--------

Now that we've algebraified truth values, we will also algebraify equality. Typically I think of equality (as in the $=$ symbol) as a metalanguage expression. Sure, we can define a relation that captures equality on a given set, but really equality is a "logical" thing, not a "mathematical" one. We'll express this using a type class in Haskell like so.

> class Equal a where
>   eq :: a -> a -> Bool

(Why not use the built in `Eq` class? No good reason.) For example, here is the ``Equal`` instance for ``Bool``:

> instance Equal Bool where
>   eq True  True  = True
>   eq True  False = False
>   eq False True  = False
>   eq False False = True
> 
> instance Equal () where
>   eq () () = True
> 
> instance Equal a => Equal (Maybe a) where
>   eq Nothing  Nothing  = True
>   eq Nothing  (Just _) = False
>   eq (Just _) Nothing  = False
>   eq (Just x) (Just y) = eq x y
> 

> 
> instance (Equal a, Equal b) => Equal (Either a b) where
>   eq (Left a1)  (Left a2)  = eq a1 a2
>   eq (Left a1)  (Right b2) = False
>   eq (Right b1) (Left a2)  = False
>   eq (Right b1) (Right b2) = eq b1 b2


Testing
-------

Suite:

> _test_boolean ::
>   ( Equal a, Arbitrary a, CoArbitrary a, Show a
>   , Boolean b, Arbitrary b, Show b, Equal b
>   )
>   => b -> a -> Int -> Int -> IO ()
> _test_boolean p x size num = do
>   testLabel0 "Bool"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args (_test_if_true p x)
>   runTest args (_test_if_false p x)
> 
>   runTest args (_test_if_func x)
>   runTest args (_test_if_nest x)
>   runTest args (_test_if_prune_left x)
>   runTest args (_test_if_prune_right x)
>   runTest args (_test_if_commute_left x)
>   runTest args (_test_if_two_args x)

Main:

> main_boolean :: IO ()
> main_boolean = _test_boolean (true :: Bool) (true :: Bool) 20 100
