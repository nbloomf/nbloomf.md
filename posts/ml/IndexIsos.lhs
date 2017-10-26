---
title: Index Isomorphisms
author: nbloomf
date: 2017-10-13
tags: ml, literate-haskell
---

First some boilerplate.

> {-# LANGUAGE LambdaCase #-}
> module IndexIsos where
> 
> import Data.List
> import Test.QuickCheck
> import Test.QuickCheck.Test
> import System.Exit
> 
> import Indices

Our ``Size`` type has a derived notion of structural equality; two sizes are equal if they are represented by the same constructor tree. It will also be handy to have a more forgiving kind of equivalence which takes into account the usual identities on semirings. Concretely, the sizes $(a+b)+c$ and $a+(b+c)$ are not equal, but we'd like to say they are equivalent. We can do this by putting ``Size``s into a canonical form using the semiring identities so that two sizes are equivalent if and only if they have the same canonical form.

To give away the punchline, this module exports two important functions: ``~=``, which detects when two sizes are canonically equivalent, and ``mapIndex``, which provides a canonical isomorphism between the index sets of equivalent sizes. The code looks a little hideous, but what's really going on is a solution to the word problem for free semirings, with some extra bookkeeping.

Looking ahead, we'll use the code here to help define equality on tensors.


Equivalence
-----------

We can think of elements in $\mathbb{S}$ like polynomials in the "variables" 0, 1, 2, and so on. Polynomials have a nice canonical form; we can completely expand them out as a sum of products using the distributive property over and over, and then sort the terms lexicographically using the commutative property of addition. We can approximate this for ``Size``s, using nested lists to represent sums of products. Note that multiplication is not commutative for our purposes.

This is more or less the algorithm for putting a polynomial in canonical form from college algebra, but for a more general and rigorous proof check out [Word Problem for Ringoids of Numerical Functions](http://www.ams.org/journals/tran/1971-158-02/S0002-9947-1971-0280375-3/S0002-9947-1971-0280375-3.pdf) by Iskander.

> canon :: Size -> [[Integer]]
> canon (Size k) = case k of
>   0 -> [   ]
>   1 -> [[ ]]
>   _ -> [[k]]
> canon (u :+ v) =
>   sort $ (canon u) ++ (canon v)
> canon (u :* v) =
>   sort [ x ++ y | x <- canon u, y <- canon v ]

Now two sizes are equivalent if they have the same canonical form.

> class Equiv t where
>   (~=) :: t -> t -> Bool
> 
>   (~/=) :: t -> t -> Bool
>   a ~/= b = not (a ~= b)
> 
> instance Equiv Size where
>   u ~= v = (canon u) == (canon v)

Testing ``~=`` amounts to testing that ``Size`` satisfies the usual axioms of arithmetic up to equivalence, sans commutativity for multiplication. (More precisely, the semiring axioms.)

> _test_size_plus_zero
>   :: Test (Size -> Bool)
> _test_size_plus_zero =
>   testName "u :+ 0 ~= u and 0 :+ u ~= u" $
>   \u -> and
>     [ (u :+ 0) ~= u
>     , (0 :+ u) ~= u
>     ]
> 
> _test_size_times_zero
>   :: Test (Size -> Bool)
> _test_size_times_zero =
>   testName "u :* 0 ~= 0 and 0 :* u ~= 0" $
>   \u -> and
>     [ (u :* 0) ~= 0
>     , (0 :* u) ~= 0
>     ]
> 
> _test_size_times_one
>   :: Test (Size -> Bool)
> _test_size_times_one =
>   testName "u :* 1 ~= u and 1 :* u ~= u" $
>   \u -> and
>     [ (u :* 1) ~= u
>     , (1 :* u) ~= u
>     ]
> 
> _test_size_equiv_plus_comm
>   :: Test (Size -> Size -> Bool)
> _test_size_equiv_plus_comm =
>   testName "(u :+ v)  ~=  (v :+ u)" $
>   \u v ->
>     (u :+ v) ~= (v :+ u)
> 
> _test_size_equiv_plus_assoc
>   :: Test (Size -> Size -> Size -> Bool)
> _test_size_equiv_plus_assoc =
>   testName "(u :+ v) :+ w  ~=  u :+ (v :+ w)" $
>   \u v w ->
>     ((u :+ v) :+ w) ~= (u :+ (v :+ w))
> 
> _test_size_equiv_times_assoc
>   :: Test (Size -> Size -> Size -> Bool)
> _test_size_equiv_times_assoc =
>   testName "(u :* v) :* w  ~=  u :* (v :* w)" $
>   \u v w ->
>     ((u :* v) :* w) ~= (u :* (v :* w))
> 
> _test_size_equiv_dist
>   :: Test (Size -> Size -> Size -> Bool)
> _test_size_equiv_dist =
>   testName "u :* (v :+ w) ~= (u :* v) :+ (u :* w)" $
>   \u v w -> and
>     [ (u :* (v :+ w)) ~= ((u :* v) :+ (u :* w))
>     , ((u :+ v) :* w) ~= ((u :* w) :+ (v :* w))
>     ]


What About Indices?
-------------------

This is nice and all -- we can tell when two tensor sizes are canonically equivalent. This alone is not enough, though. If two sizes are equivalent, there is a canonical isomorphism between their index sets, and to make equivalence useful we need to be able to construct this isomorphism. For that we need to know <em>what steps</em> are required to put a size in canonical form. This is sort of analogous to the problem of putting a matrix in Gauss-Jordan form, where keeping track of the steps taken in the Gauss-Jordan elimination algorithm lets us construct a witness to the row-equivalence of two matrices.

Each semiring identity represents one or two "moves" we can apply to a ``Size``; one if the identity is symmetric, and two if not.

> data Op
>   = PlusComm          -- a+b         => b+a
>   | PlusAssocL        -- a+(b+c)     => (a+b)+c
>   | PlusAssocR        -- (a+b)+c     => a+(b+c)
>   | PlusZeroL         -- a           => 0+a
>   | UnPlusZeroL       -- 0+a         => a
>   | PlusZeroR         -- a           => a+0
>   | UnPlusZeroR       -- a+0         => a
>   | TimesAssocL       -- a*(b*c)     => (a*b)*c
>   | TimesAssocR       -- (a*b)*c     => a*(b*c)
>   | TimesOneL         -- a           => 1*a
>   | UnTimesOneL       -- 1*a         => a
>   | TimesOneR         -- a           => a*1
>   | UnTimesOneR       -- a*1         => a
>   | TimesZeroL Size   -- 0           => 0*a
>   | UnTimesZeroL Size -- 0*a         => 0
>   | TimesZeroR Size   -- 0           => a*0
>   | UnTimesZeroR Size -- a*0         => 0
>   | DistL             -- a*(b+c)     => (a*b)+(a*c)
>   | UnDistL           -- (a*b)+(a*c) => a*(b+c)
>   | DistR             -- (a+b)*c     => (a*c)+(b*c)
>   | UnDistR           -- (a*c)+(b*c) => (a+b)*c
>   | LSummand Op       -- a => b --> a+c => b+c
>   | RSummand Op       -- a => b --> c+a => c+b
>   | LFactor Op        -- a => b --> a*c => b*c
>   | RFactor Op        -- a => b --> c*a => c*b
>   deriving (Eq, Show)

(Most of the functions in this post will be partial, but the error cases should be unreachable if used correctly.)

And we can actually apply ``Op``s to ``Size``s like so.

> applyOp :: Op -> Size -> Size
> applyOp op size = case (op, size) of
>   (PlusComm,       u :+ v         ) -> v :+ u
>   (PlusAssocL,     u :+ (v :+ w)  ) -> (u :+ v) :+ w
>   (PlusAssocR,     (u :+ v) :+ w  ) -> u :+ (v :+ w)
>   (PlusZeroL,      u              ) -> 0 :+ u
>   (UnPlusZeroL,    (Size 0) :+ u  ) -> u
>   (PlusZeroR,      u              ) -> u :+ 0
>   (UnPlusZeroR,    u :+ (Size 0)  ) -> u
>   (TimesAssocL,    u :* (v :* w)  ) -> (u :* v) :* w
>   (TimesAssocR,    (u :* v) :* w  ) -> u :* (v :* w)
>   (TimesOneL,      a              ) -> 1 :* a
>   (UnTimesOneL,    (Size 1) :* a  ) -> a
>   (TimesOneR,      a              ) -> a :* 1
>   (UnTimesOneR,    a :* (Size 1)  ) -> a
>   (TimesZeroL s,   Size 0         ) -> 0 :* s
>   (UnTimesZeroL s, (Size 0) :* a  ) ->
>     if a == s
>       then 0
>       else error "applyOp (unTimesZeroL): size mismatch"
>   (TimesZeroR s,   Size 0         ) -> s :* 0
>   (UnTimesZeroR s, a :* (Size 0)  ) ->
>     if a == s
>       then 0
>       else error "applyOp (unTimesZeroR): size mismatch"
>   (DistL,          a :* (b :+ c)  ) -> (a :* b) :+ (a :* c)
>   (UnDistL,        (a:*b):+(d:*c) ) ->
>     if a == d
>       then a:*(b:+c)
>       else error "applyOp (UnDistL): size mismatch"
>   (DistR,          (a :+ b) :* c  ) -> (a :* c) :+ (b :* c)
>   (UnDistR,        (a:*c):+(b:*d) ) ->
>     if c == d
>       then (a:+b):*c
>       else error "applyOp (UnDistR): size mismatch"
>   (LSummand x,     a :+ b         ) -> (applyOp x a) :+ b
>   (RSummand x,     a :+ b         ) -> a :+ (applyOp x b)
>   (LFactor x,      a :* b         ) -> (applyOp x a) :* b
>   (RFactor x,      a :* b         ) -> a :* (applyOp x b)
>   _ -> error $ "applyOp: " ++ show op ++ " " ++ show size

In practice we'll be applying lists of ``Op``s, which can be done with ``foldr``. Note that ``reverse``; we'll assume lists of ``Op``s come in order from head to tail, and we need to reverse the ops list due to how foldr works.

> applyOps :: [Op] -> Size -> Size
> applyOps ops size = foldr applyOp size (reverse ops)

Each ``Op`` has an inverse which undoes it.

> invertOp :: Op -> Op
> invertOp = \case
>   PlusComm       -> PlusComm
>   PlusAssocL     -> PlusAssocR
>   PlusAssocR     -> PlusAssocL
>   PlusZeroL      -> UnPlusZeroL
>   UnPlusZeroL    -> PlusZeroL
>   PlusZeroR      -> UnPlusZeroR
>   UnPlusZeroR    -> PlusZeroR
>   TimesAssocL    -> TimesAssocR
>   TimesAssocR    -> TimesAssocL
>   TimesOneL      -> UnTimesOneL
>   UnTimesOneL    -> TimesOneL
>   TimesOneR      -> UnTimesOneR
>   UnTimesOneR    -> TimesOneR
>   TimesZeroL s   -> UnTimesZeroL s
>   UnTimesZeroL s -> TimesZeroL s
>   TimesZeroR s   -> UnTimesZeroR s
>   UnTimesZeroR s -> TimesZeroR s
>   DistL          -> UnDistL
>   UnDistL        -> DistL
>   DistR          -> UnDistR
>   UnDistR        -> DistR
>   LSummand op    -> LSummand $ invertOp op
>   RSummand op    -> RSummand $ invertOp op
>   LFactor op     -> LFactor $ invertOp op
>   RFactor op     -> RFactor $ invertOp op

And we can invert sequences of ``Op``s.

> invertOps :: [Op] -> [Op]
> invertOps ops = map invertOp (reverse ops)

Later we'll want to test assertions like "applying these operations to $u$ results in $v$". We'll write a helper test here to check this.

> _test_ops_equivalent :: Size -> Size -> [Op] -> Bool
> _test_ops_equivalent s t ops = and
>   [ t == applyOps ops s
>   , s == applyOps (invertOps ops) t
>   ]

Ok! To find the sequence of ``Op``s needed to put a ``Size`` in canonical form, we'll break the usual college algebra procedure into phases.

1. "Expand" the size using the distributive identities over and over, so that all the plus nodes appear toward the root and all the times notes appear toward the leaves. (If any times node appears above a plus node, we can use distributivity to switch them.)
2. "Prune" the size by eliminating any instances of "plus zero", "times one", or "times zero". Pruning an expanded tree gives another expanded tree.
3. "Unbalance" the size by pushing all nested sizes to the right using the associative identities. Unbalancing a pruned and expanded tree gives another pruned and expanded tree.
4. "Arrange" the summands in graded lex order using associativity and commutativity.

Doing all four steps in order, and keeping track of which identities we use, gives a canonical form as well as a recipe for how to get there.


Expand
------

A ``Size`` is <em>expanded</em> if no sum node appears below a product node. We can detect this with the predicate ``isExpanded``.

> isExpanded :: Size -> Bool
> isExpanded s =
>   if isProduct s
>     then True
>     else case s of
>       a :+ b -> (isExpanded a) && (isExpanded b)
>       _ -> error $ "isExpanded (unreachable): " ++ show s
> 
> isProduct :: Size -> Bool
> isProduct = \case
>   Size _ -> True
>   a :+ b -> False
>   a :* b -> (isProduct a) && (isProduct b)

Now ``expand u`` finds an expanded ``Size`` that is equivalent to ``u``, and a sequence of identities that witnesses their equivalence.

> expand :: Size -> (Size, [Op])
> expand (Size k) =
>   (Size k, [])
> 
> expand (a :+ b) =
>   let
>     (u,uOps') = expand a
>     (v,vOps') = expand b
>     uOps = map LSummand uOps'
>     vOps = map RSummand vOps'
>   in
>     (u :+ v, uOps ++ vOps)
> 
> expand (a :* b) =
>   let
>     (u,uOps') = expand a
>     (v,vOps') = expand b
>     uOps = map LFactor uOps'
>     vOps = map RFactor vOps'
>   in
>     case (u,v) of
>       (h' :+ k', _) ->
>         let
>           (h, hOps') = expand (h' :* v)
>           (k, kOps') = expand (k' :* v)
>           hOps = map LSummand hOps'
>           kOps = map RSummand kOps'
>         in
>           (h :+ k, uOps ++ vOps ++ [DistR] ++ hOps ++ kOps)
>       (_, h' :+ k') ->
>         let
>           (h, hOps') = expand (u :* h')
>           (k, kOps') = expand (u :* k')
>           hOps = map LSummand hOps'
>           kOps = map RSummand kOps'
>         in
>           (h :+ k, uOps ++ vOps ++ [DistL] ++ hOps ++ kOps)
>       _ -> (u :* v, uOps ++ vOps)

And we can test that (1) ``expand u`` gives a size ``v`` in expanded form and (2) ``u`` and ``v`` are equivalent using the witness.

> _test_expand :: Test (Size -> Bool)
> _test_expand =
>   testName "expand" $
>   \u ->
>     let
>       (v, vOps) = expand u
>       ops = vOps
>     in
>       and
>         [ isExpanded v
>         , _test_ops_equivalent u v ops
>         ]


Prune
-----

A ``Size`` is <em>pruned</em> if it does not feature a "plus zero", "times one", or "times zero". We can detect this with ``isPruned``.

> isPruned :: Size -> Bool
> isPruned = \case
>   Size k -> True
>   a :+ b ->
>     if a == 0 || b == 0
>       then False
>       else (isPruned a) && (isPruned b)
>   a :* b ->
>     if a == 0 || b == 0 || a == 1 || b == 1
>       then False
>       else (isPruned a) && (isPruned b)

Now ``prune u`` finds a pruned ``Size`` that is equvalent to ``u``, and a sequence of identities that witnesses their equivalence.

> prune :: Size -> (Size, [Op])
> prune (Size k) =
>   (Size k, [])
> 
> prune (a :+ b) =
>   let
>     (u,uOps') = prune a
>     (v,vOps') = prune b
>     uOps = map LSummand uOps'
>     vOps = map RSummand vOps'
>   in
>     case (u,v) of
>       (Size 0, _     ) -> (v,      uOps ++ vOps ++ [UnPlusZeroL])
>       (_,      Size 0) -> (u,      uOps ++ vOps ++ [UnPlusZeroR])
>       _                -> (u :+ v, uOps ++ vOps)
> 
> prune (a :* b) =
>   let
>     (u, uOps') = prune a
>     (v, vOps') = prune b
>     uOps = map LFactor uOps'
>     vOps = map RFactor vOps'
>   in
>     case (u,v) of
>       (Size 0, _     ) -> (Size 0, uOps ++ vOps ++ [UnTimesZeroL v])
>       (_,      Size 0) -> (Size 0, uOps ++ vOps ++ [UnTimesZeroR u])
>       (Size 1, _     ) -> (v,      uOps ++ vOps ++ [UnTimesOneL])
>       (_,      Size 1) -> (u,      uOps ++ vOps ++ [UnTimesOneR])
>       _                -> (u :* v, uOps ++ vOps)

And we can test that, after expanding and pruning, we get an equivalent expanded and pruned size.

> _test_prune :: Test (Size -> Bool)
> _test_prune =
>   testName "prune" $
>   \u ->
>     let
>       (v, vOps) = expand u
>       (w, wOps) = prune v
>       ops = vOps ++ wOps
>     in
>       and
>         [ isPruned w && isExpanded w
>         , _test_ops_equivalent u w ops
>         ]


Unbalance
---------

A ``Size`` is <em>unbalanced</em> if no sum node appears in the left subtree of another sum node, and no product node appears in the left subtree of another product node. We can detect this with the predicate ``isUnbalanced``.

> isUnbalanced :: Size -> Bool
> isUnbalanced = \case
>   Size k -> True
>   u :+ v -> (isUnbalancedProduct u) && (isUnbalanced v)
>   u -> isUnbalancedProduct u
> 
> isUnbalancedProduct :: Size -> Bool
> isUnbalancedProduct = \case
>   Size k -> True
>   (Size k) :* v -> isUnbalancedProduct v
>   _ -> False

Now ``unbalance u`` takes an expanded and pruned ``Size`` and finds an equivalent expanded, pruned, and unbalanced ``Size``, with a witness to their equivalence.

> -- assumes isExpanded u == True
> unbalance :: Size -> (Size, [Op])
> unbalance = \case
>   Size k -> (Size k, [])
>   (Size k) :* (Size l) -> ((Size k) :* (Size l), [])
>   (Size k) :* b ->
>     let
>       (v, vOps') = unbalance b
>       vOps = map RFactor vOps'
>     in ((Size k) :* v, vOps)
>   (a :* b) :* c ->
>     let
>       ((Size k) :* u, uOps') = unbalance (a :* b)
>       uOps = map LFactor uOps'
>       (d, dOps') = unbalance (u :* c)
>       dOps = map RFactor dOps'
>     in ((Size k) :* d, uOps ++ [TimesAssocR] ++ dOps)
>   (Size k) :+ b ->
>     let
>       (v, vOps') = unbalance b
>       vOps = map RSummand vOps'
>     in ((Size k) :+ v, vOps)
>   a@(_ :* _) :+ b ->
>     let
>       (u, uOps') = unbalance a
>       uOps = map LSummand uOps'
>       (v, vOps') = unbalance b
>       vOps = map RSummand vOps'
>     in (u :+ v, uOps ++ vOps)
>   (a :+ b) :+ c ->
>     let
>       (u :+ w, uOps') = unbalance (a :+ b)
>       uOps = map LSummand uOps'
>       (d, dOps') = unbalance (w :+ c)
>       dOps = map RSummand dOps'
>     in (u :+ d, uOps ++ [PlusAssocR] ++ dOps)

We can test that, after expanding, pruning, and unbalancing, we get an equivalent expanded, pruned, and unbalanced size.

> _test_unbalance :: Test (Size -> Bool)
> _test_unbalance =
>   testName "unbalance" $
>   \u ->
>     let
>       (v, vOps) = expand u
>       (w, wOps) = prune v
>       (x, xOps) = unbalance w
>       ops = vOps ++ wOps ++ xOps
>     in
>       and
>         [ isUnbalanced x && isPruned x && isExpanded x
>         , _test_ops_equivalent u x ops
>         ]


Arrange
-------

An unbalanced ``size`` is <em>arranged</em> if its terms are sorted by the graded lexicographic order. We can detect this with ``isArranged``.

> -- assumes isUnbalanced s == True
> isArranged :: Size -> Bool
> isArranged = \case
>   a :+ b ->
>     (glexleq a (minterm b)) && (isArranged b)
>   _ -> True
> 
> glexleq :: Size -> Size -> Bool
> glexleq u v = case (u,v) of
>   (Size k, Size l) -> k <= l
>   (Size _, _     ) -> True
>   (_     , Size _) -> False
>   ((Size k) :* u, (Size l) :* v) ->
>     (k < l) || ((k == l) && (glexleq u v))
>   _ -> error "glexleq: only works on unbalanced products"
> 
> minterm :: Size -> Size
> minterm = \case
>   a :+ (b :+ c) ->
>     let m = minterm (b :+ c) in
>     if glexleq a m then a else m
>   a :+ b -> if glexleq a b then a else b
>   s -> s

Now ``arrange u`` takes an expanded, pruned, and unbalanced ``Size`` and finds an equivalent expanded, pruned, unbalanced, and arranged ``Size``, with a witness to their equivalence.

> -- assumes isUnbalanced s == True
> arrange :: Size -> (Size, [Op])
> arrange (a :+ (b :+ c)) =
>   let
>     (u :+ v, uvOps') = arrange (b :+ c)
>     uvOps = map RSummand uvOps'
>   in
>     if glexleq a u
>       then (a :+ (u :+ v), uvOps)
>       else
>         let
>           (w, wOps') = arrange (a :+ v)
>           wOps = map RSummand wOps'
>         in
>           ( u :+ w
>           , uvOps ++ [PlusAssocL, LSummand PlusComm, PlusAssocR] ++ wOps
>           )
> arrange (a :+ b) =
>   if glexleq a b
>     then (a :+ b, [])
>     else (b :+ a, [PlusComm])
> arrange s = (s, [])

We can test that, after expanding, pruning, unbalancing, and arranging, we get an equivalent expanded, pruned, unbalanced, and arranged size.

> _test_arrange :: Test (Size -> Bool)
> _test_arrange =
>   testName "arrange" $
>   \u ->
>     let
>       (v, vOps) = expand u
>       (w, wOps) = prune v
>       (x, xOps) = unbalance w
>       (y, yOps) = arrange x
>       ops = vOps ++ wOps ++ xOps ++ yOps
>     in
>       and
>         [ isArranged y && isUnbalanced y && isPruned y && isExpanded y
>         , _test_ops_equivalent u y ops
>         ]


Canonical Form, Redux
---------------------

Putting it all together, we can put sizes into canoncial form with a witness.

> toCanon :: Size -> (Size, [Op])
> toCanon s =
>   let
>     (u, uOps) = expand s
>     (v, vOps) = prune u
>     (w, wOps) = unbalance v
>     (x, xOps) = arrange w
>   in (x, uOps ++ vOps ++ wOps ++ xOps)

And a test:

> _test_toCanon :: Test (Size -> Bool)
> _test_toCanon =
>   testName "toCanon" $
>   \u ->
>     let
>       (v, ops) = toCanon u
>       (w, _) = toCanon v
>     in
>       and
>         [ u ~= v
>         , w == v
>         , _test_ops_equivalent u v ops
>         ]

And now we can find a seqence of operations between any two equivalent sizes, by combining the sequences of operations to canonical form. We do a little cancellation to remove some redundant operations.

> opsTo :: Size -> Size -> [Op]
> opsTo s t = if s ~= t
>   then
>     let
>       (u, uOps) = toCanon s
>       (v, vOps) = toCanon t
> 
>       simp :: [Op] -> [Op] -> [Op]
>       simp [] bs = bs
>       simp as [] = reverse as
>       simp (a:as) (b:bs) = if b == invertOp a
>         then simp as bs
>         else (reverse (a:as)) ++ (b:bs)
>     in
>       simp (reverse uOps) (invertOps vOps)
>   else error "sizes not canonically isomorphic"


Index Isomorphisms
------------------

We are finally prepared to construct the canonical isomorphism between two equivalent sizes. First, we nail down how a single ``Op`` acts on a single ``Index``.

> opIndex :: Op -> Index -> Index
> opIndex op index =
>   let msg = "opIndex (" ++ show op ++ "): " ++ show index in
>   case op of
>     PlusComm -> case index of
>       L i -> R i
>       R i -> L i
>       _ -> error msg
> 
>     PlusAssocL -> case index of
>       L i     -> L (L i)
>       R (L i) -> L (R i)
>       R (R i) -> R i
>       _ -> error msg
> 
>     PlusAssocR -> case index of
>       R i     -> R (R i)
>       L (R i) -> R (L i)
>       L (L i) -> L i
>       _ -> error msg
> 
>     PlusZeroL -> R index
> 
>     UnPlusZeroL -> case index of
>       R i -> i
>       _ -> error msg
> 
>     PlusZeroR -> L index
> 
>     UnPlusZeroR -> case index of
>       L i -> i
>       _ -> error msg
> 
>     TimesAssocL -> case index of
>       i :& (j :& k) -> (i :& j) :& k
>       _ -> error msg
> 
>     TimesAssocR -> case index of
>       (i :& j) :& k -> i :& (j :& k)
>       _ -> error msg
> 
>     TimesOneL -> (Index 0) :& index
> 
>     UnTimesOneL -> case index of
>       _ :& i -> i
>       _ -> error msg
> 
>     TimesOneR -> index :& (Index 0)
> 
>     UnTimesOneR -> case index of
>       i :& _ -> i
>       _ -> error msg
> 
>     TimesZeroL s ->
>       error $ msg ++ " " ++ show s
> 
>     UnTimesZeroL s ->
>       error $ msg ++ " " ++ show s
> 
>     TimesZeroR s ->
>       error $ msg ++ " " ++ show s
> 
>     UnTimesZeroR s ->
>       error $ msg ++ " " ++ show s
> 
>     DistL -> case index of
>       i :& (L j) -> L (i :& j)
>       i :& (R k) -> R (i :& k)
>       _ -> error msg
> 
>     UnDistL -> case index of
>       L (i :& j) -> i :& (L j)
>       R (i :& k) -> i :& (R k)
>       _ -> error msg
> 
>     DistR -> case index of
>       (L i) :& k -> L (i :& k)
>       (R j) :& k -> R (j :& k)
>       _ -> error msg
> 
>     UnDistR -> case index of
>       L (i :& k) -> (L i) :& k
>       R (j :& k) -> (R j) :& k
>       _ -> error msg
> 
>     LSummand o -> case index of
>       L i -> L (opIndex o i)
>       R i -> R i
>       _ -> error $ msg ++ " " ++ show o
> 
>     RSummand o -> case index of
>       R i -> R (opIndex o i)
>       L i -> L i
>       _ -> error $ msg ++ " " ++ show o
> 
>     LFactor o -> case index of
>       i :& j -> (opIndex o i) :& j
>       _ -> error $ msg ++ " " ++ show o
> 
>     RFactor o -> case index of
>       i :& j -> i :& (opIndex o j)
>       _ -> error $ msg ++ " " ++ show o

Now a list of ``Op``s acts like a ``foldr``.

> opsIndex :: [Op] -> Index -> Index
> opsIndex ops index = foldr opIndex index (reverse ops)

And ``mapIndex`` is the canonical isomorphism.

> mapIndex :: Size -> Size -> Index -> Index
> mapIndex s t = if s ~= t
>   then opsIndex (opsTo s t)
>   else error "mapIndex: sizes must be canonically equivalent"

The most important property to test for ``mapIndex`` is that it is actually an isomorphism; the following helper function does this.

> _test_mapIndex_iso :: Size -> Size -> Bool
> _test_mapIndex_iso s t = and
>   [ and [ i == mapIndex t s (mapIndex s t i) | i <- indicesOf s ]
>   , and [ i == mapIndex s t (mapIndex t s i) | i <- indicesOf t ]
>   ]

For example, ``mapIndex`` should give an isomorphism for the indices of any size $u$ and its canonical form.

> _test_mapIndex_toCanon :: Test (Size -> Bool)
> _test_mapIndex_toCanon =
>   testName "mapIndex toCanon" $
>   \u ->
>     let
>       (v, _) = toCanon u
>     in
>       _test_mapIndex_iso u v

And the canonical isomorphism from ``u`` to ``u`` should be the identity.

> _test_mapIndex_self :: Test (Size -> Bool)
> _test_mapIndex_self =
>   testName "mapIndex u u == id" $
>   \u ->
>     all (\i -> i == mapIndex u u i) (indicesOf u)

For good measure we can also test ``mapIndex`` against the semiring identities.

> _test_mapIndex_plus_zero :: Test (Size -> Bool)
> _test_mapIndex_plus_zero =
>   testName "mapIndex plus zero" $
>   \u -> and
>     [ _test_mapIndex_iso u (0 :+ u)
>     , _test_mapIndex_iso u (u :+ 0)
>     ]
> 
> _test_mapIndex_times_zero :: Test (Size -> Bool)
> _test_mapIndex_times_zero =
>   testName "mapIndex times zero" $
>   \u -> and
>     [ _test_mapIndex_iso 0 (0 :* u)
>     , _test_mapIndex_iso 0 (u :* 0)
>     ]
> 
> _test_mapIndex_times_one :: Test (Size -> Bool)
> _test_mapIndex_times_one =
>   testName "mapIndex times one" $
>   \u -> and
>     [ _test_mapIndex_iso u (1 :* u)
>     , _test_mapIndex_iso u (u :* 1)
>     ]
> 
> _test_mapIndex_plus_comm :: Test (Size -> Size -> Bool)
> _test_mapIndex_plus_comm =
>   testName "mapIndex plus comm" $
>   \u v -> _test_mapIndex_iso (u :+ v) (v :+ u)
> 
> _test_mapIndex_plus_assoc :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_plus_assoc =
>   testName "mapIndex plus assoc" $
>   \u v w -> _test_mapIndex_iso ((u :+ v) :+ w) (u :+ (v :+ w))
> 
> _test_mapIndex_times_assoc :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_times_assoc =
>   testName "mapIndex times assoc" $
>   \u v w -> _test_mapIndex_iso ((u :* v) :* w) (u :* (v :* w))
> 
> _test_mapIndex_dist :: Test (Size -> Size -> Size -> Bool)
> _test_mapIndex_dist =
>   testName "mapIndex dist" $
>   \u v w -> and
>     [ _test_mapIndex_iso (u :* (v :+ w)) ((u :* v) :+ (u :* w))
>     , _test_mapIndex_iso ((u :+ v) :* w) ((u :* w) :+ (v :* w))
>     ]


Tests
-----

> _test_index_isos :: Int -> Int -> IO ()
> _test_index_isos num size = do
>   testLabel "Size and Index"
> 
>   let
>     args = stdArgs
>       { maxSuccess = num
>       , maxSize = size
>       }
> 
>   runTest args _test_size_plus_zero
>   runTest args _test_size_times_zero
>   runTest args _test_size_times_one
>   runTest args _test_size_equiv_plus_comm
>   runTest args _test_size_equiv_plus_assoc
>   runTest args _test_size_equiv_times_assoc
>   runTest args _test_size_equiv_dist
> 
>   runTest args _test_expand
>   runTest args _test_prune
>   runTest args _test_unbalance
>   runTest args _test_arrange
>   runTest args _test_toCanon
> 
>   runTest args _test_mapIndex_toCanon
>   runTest args _test_mapIndex_self
>   runTest args _test_mapIndex_plus_zero
>   runTest args _test_mapIndex_times_zero
>   runTest args _test_mapIndex_times_one
>   runTest args _test_mapIndex_plus_comm
>   runTest args _test_mapIndex_plus_assoc
>   runTest args _test_mapIndex_times_assoc
>   runTest args _test_mapIndex_dist
> 
> main_index_isos :: IO ()
> main_index_isos = _test_index_isos 100 10
