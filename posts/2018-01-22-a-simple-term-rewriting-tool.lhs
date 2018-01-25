---
title: A simple term rewriting tool
author: nbloomf
date: 2018-01-23
tags: literate-haskell
---

> module TermRewriting where
> 
> import Data.List (nub, unfoldr)
> import Data.Maybe (catMaybes)
> import Text.ParserCombinators.Parsec
> import System.Environment
> import System.Exit

Today we'll build a tool that applies term-rewriting rules to expressions in a simplified form of mathematical notation.

My motivation for this comes from the Arithmetic Made Difficult series of posts on this site. There, I'm writing lots of equation-style proofs, and it would be nice to have a tool check that at least some of the steps in those proofs are carried out correctly. I won't try to build a full-fledged proof checker -- building a proof checker that uses a syntax readable by people is a Hard Problem. But a simple term rewriting tool can get us (made up number) 80% of the benefits with 1% of the effort.


Grammar
-------

To set the scope of the problem, we'll focus on a subset of math notation that can be easily translated to something like lambda calculus. The basic ingredients are

1. *constants*, or atomic expressions;
2. *variables*, for which we can substitute subexpressions; and
3. *application* of one expression to another.

Syntactically, we will decree that constants consist of one or more letters prefixed by a `\`, such as

    \plus \times \cons

We'll decree that variables consist of one or more letters *not* prefixed by a `\`, such as

    a b foo munge

Application is a little trickier. Certainly an expression like ``f(a)`` means "the expression ``f`` applied to the expression ``a``. The trouble is how to handle functions with more than one argument. We'll do this by implicitly currying all functions. Remember that any function with signature

    f : (a,b) -> c

is equivalent to one with signature

    g : a -> b -> c

where the function arrow is right associative. So we can interpret an expression like ``f(a,b)`` implicitly as ``f(a)(b)``. In particular, we only need to support functions of one argument.

We can represent this little grammar with the following ``Expr`` type.

> data Expr
>   = Constant Token
>   | Variable Token
>   | Apply Expr Expr
>   deriving (Eq, Show)
> 
> type Token = String

Nothing about this type is specific to LaTeX, but we can write a little parser to read LaTeX statements in to the ``Expr`` type. We'll go ahead and do this now so we can define ``Expr`` values more easily.

> pLatexExpr :: Parser Expr
> pLatexExpr = chainl1 pTerm (return Apply)
>   where
>     parens, braces :: Parser a -> Parser a
>     parens = between (char '(') (char ')')
>     braces = between (char '{') (char '}')
> 
>     pVariable :: Parser Expr
>     pVariable = do
>       token <- many1 letter
>       args <- option [] $ parens $ sepBy1 pLatexExpr (char ',')
>       case args of
>         [] -> return $ Variable token
>         as -> return $ foldl Apply (Variable token) as
> 
>     pConstant :: Parser Expr
>     pConstant = do
>       char '\\'
>       token <- many1 letter
>       args <- option [] $ parens $ sepBy1 pLatexExpr (char ',')
>       case args of
>         [] -> return $ Constant token
>         as -> return $ foldl Apply (Constant token) as
> 
>     pTerm :: Parser Expr
>     pTerm = choice
>       [ parens pLatexExpr
>       , braces pLatexExpr
>       , pConstant
>       , pVariable
>       ]

And some helpers:

> parseWith :: String -> Parser a -> String -> Either String a
> parseWith loc p text = case runParser (p <* eof) () loc text of
>   Left err -> Left (show err)
>   Right x -> Right x
> 
> parseWithIO :: String -> Parser a -> String -> IO a
> parseWithIO loc p text = case parseWith loc p text of
>   Left msg -> putStrLn (unwords [loc,msg]) >> exitFailure
>   Right a  -> return a

And here is an example.

```haskell
$> x <- parseWithIO "" pLatexExpr "\\plus(a,\\times(b,c))"
$> putStrLn $ show x
Apply (Apply (Constant "plus") (Variable "a")) (Apply (Apply (Constant "times") (Variable "b")) (Variable "c"))
```

We'll also make a function to pretty print ``Expr``s as LaTeX.

> latex :: Expr -> String
> latex (Constant x) = '\\' : x
> latex (Variable x) = x
> latex (Apply x y) = concat
>   [ latex x, "(", latex y, ")" ]

For example:

```haskell
$> x <- parseWithIO "" pLatexExpr "\\plus(a,\\times(b,c))"
$> putStrLn $ latex x
\plus(a)(\times(b)(c))
```

Note that the round trip generally takes a LaTeX statement to a different, but equivalent, statement. This is the price of simplicity, and doesn't matter too much.


Substitutions
-------------

A *substitution* is a mapping from variables to expressions, which we'll represent using as a list of pairs.

> type Substitution = [(Token, Expr)]

Since lists are not actually maps, we need a helper function to decide whether a given list of token-expression pairs is well-defined. That is, we shouldn't have two pairs with the same token but different expressions.

> wellDefined :: Substitution -> Bool
> wellDefined [] = True
> wellDefined ((x,a):ps) = and
>   [ null (filter (\(y,b) -> (x == y) && (a /= b)) ps)
>   , wellDefined ps
>   ]

Now actually making a substitution is straightforward.

> substitute :: Substitution -> Expr -> Expr
> substitute _  (Constant a) =
>   Constant a
> substitute es (Variable x) =
>   case lookup x es of
>     Just e  -> e
>     Nothing -> Variable x
> substitute es (Apply a b) =
>   Apply (substitute es a) (substitute es b)

For fun:

> showSub :: Substitution -> String
> showSub x = unlines $ map (\(a,z) -> a ++ " => " ++ latex z) x

Next we can try to construct a substitution taking one expression to another, based at the root.

> matches :: Expr -> Expr -> Maybe Substitution
> matches pattern expr = match' pattern expr >>= check
>   where
>     check ps = if wellDefined ps
>       then Just (nub ps)
>       else Nothing
> 
>     match' (Constant a) (Constant b) =
>       if a == b then Just [] else Nothing
>     match' (Constant _) _ =
>       Nothing
>     match' (Variable x) e =
>       Just [(x,e)]
>     match' (Apply e1 e2) (Apply f1 f2) = do
>       xs <- match' e1 f1
>       ys <- match' e2 f2
>       return (xs ++ ys)
>     match' (Apply _ _) _ =
>       Nothing

More generally matches can occur anywhere in an expression, and we need to be able to unambiguously state where the match is. The ``Path`` type represents a series of directions for moving from the root of an expression to some interior node.

> data Path
>   = H | L Path | R Path
>   deriving (Eq, Show)

And ``matchesIn`` constructs a list of all substitutions from one expression to another, along with paths to the root of each substitution.

> matchesIn :: Expr -> Expr -> [(Path, Substitution)]
> matchesIn pattern expr = case expr of
>   Constant a -> case matches pattern expr of
>     Nothing -> []
>     Just s -> [(H, s)]
>   Variable x -> case matches pattern expr of
>     Nothing -> []
>     Just s -> [(H, s)]
>   Apply x y -> do
>     let
>       mx = map (\(p,z) -> (L p, z)) $ matchesIn pattern x
>       my = map (\(p,z) -> (R p, z)) $ matchesIn pattern y
>     case matches pattern expr of
>       Nothing -> mx ++ my
>       Just s -> (H,s) : mx ++ my

Given a ``Path``, we can (attempt to) transform the subexpression it points to.

> transform :: (Expr -> Expr) -> Path -> Expr -> Maybe Expr
> transform f H expr = Just (f expr)
> transform f (L path) (Apply expr w) = do
>   q <- transform f path expr
>   Just (Apply q w)
> transform f (R path) (Apply w expr) = do
>   q <- transform f path expr
>   Just (Apply w q)
> transform _ _ _ = Nothing
> 
> rewrite :: Expr -> Path -> Expr -> Maybe Expr
> rewrite p = transform (const p)


Rewrite Rules
-------------

A *rewrite rule* is a pair of expressions that we interpret as being "equal" for all possible substitutions.

> type Rule = (Expr, Expr)
> 
> pRule :: Parser Expr -> Parser Rule
> pRule p = do
>   a <- p
>   spaces
>   char '='
>   spaces
>   b <- p
>   return (a,b)

> validate1 :: Rule -> Expr -> Expr -> (Path, Substitution) -> Bool
> validate1 (_,q) h k (path,subs) =
>   case rewrite (substitute subs q) path h of
>     Nothing -> False
>     Just w -> w == k
> 
> validate :: Rule -> Expr -> Expr -> [(Path, Substitution)]
> validate (p,q) h k =
>   filter (validate1 (p,q) h k) (matchesIn p h)


Interface
---------

We'll keep this really simple. This tool expects its input on `stdin`, one rewrite check per line, in the form

    location TAB rulelhs = rulerhs TAB from-expr TAB to-expr

So we'll need to split a line on tabs:

> unTab :: String -> [String]
> unTab = unfoldr getCell
>   where
>     getCell [] = Nothing
>     getCell xs =
>       let
>         (cell, z) = span (/= '\t') xs
>         rest = if null z then [] else tail z
>       in
>         Just (cell, rest)

And we'll need to process one untabbed line. We're assuming that the rewrite rules are reversible; given `x = y` and two expressions `lhs` and `rhs`, any substitution taking either `lhs` to `rhs` or `rhs` to `lhs` is considered valid. This is ok for the equation chains we want to use this on in the Arithmetic Made Difficult posts.

> process :: [String] -> IO ()
> process [loc,r,a,b] = do
>   (x,y) <- parseWithIO loc (pRule pLatexExpr) r
>   lhs <- parseWithIO loc pLatexExpr a
>   rhs <- parseWithIO loc pLatexExpr b
>   case (validate (x,y) lhs rhs, validate (y,x) lhs rhs, validate (x,y) rhs lhs, validate (y,x) lhs rhs) of
>     ([],[],[],[]) -> do
>       putStrLn $ unwords [loc,"invalid!",r,"::",a,"-->",b]
>     _ -> return ()
> process xs = do
>   putStrLn $ unwords ("unrecognized input:":xs)

Now the main tool just splits each input line and verifies rewrites.

> main :: IO ()
> main = do
>   checks <- fmap (map unTab . lines) getContents
>   mapM_ process checks
