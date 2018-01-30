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
> import Control.Monad (guard)
> import Text.ParserCombinators.Parsec
> import System.Environment
> import System.Exit
> import System.IO

Today we'll build a tool that applies term-rewriting rules to expressions in a simplified form of mathematical notation.

My motivation for this comes from the [Arithmetic Made Difficult](/pages/amd.html) series of posts on this site. There, I'm writing lots of equation-style proofs, and it would be nice to have a tool check that at least some of the steps in those proofs are carried out correctly. I won't try to build a full-fledged proof checker -- building a proof checker that uses a syntax readable by people is a Hard Problem. But a simple term rewriting tool can get us (made up number) 80% of the benefits with 1% of the effort. With this tool, we'll be able to annotate equational proofs with "justification" information that is machine checked, but also compiles to human readable cross references (hyperlinks).


Grammar
-------

To set the scope of the problem, we'll focus on a subset of math notation that can be easily translated to something like lambda calculus. The basic ingredients are

1. *constants*, or atomic expressions, that represent themselves;
2. *variables*, that represent arbitrary subexpressions; and
3. *application* of one expression to another.

We can represent this little grammar with the following ``Expr`` type.

> data Expr
>   = Con Token
>   | Var Token
>   | App Expr Expr
>   deriving (Eq, Show)
> 
> type Token = String

In keeping with $\LaTeX$ syntax, we will decree that constants consist of one or more letters prefixed by a `\`, such as

    \plus \times \cons

> pCon :: Parser Expr
> pCon = do
>   char '\\'
>   token <- many1 letter
>   return (Con token)

We'll decree that variables consist of one or more letters *not* prefixed by a `\`, such as

    a b foo munge

> pVar :: Parser Expr
> pVar = do
>   token <- many1 letter
>   return (Var token)

Application is a little trickier. Certainly an expression like ``f(a)`` means "the expression ``f`` applied to the expression ``a``. The trouble is how to handle functions with more than one argument. We'll do this by implicitly currying all functions. Remember that any function with signature

    f : (a,b) -> c

is equivalent to one with signature

    g : a -> b -> c

where the function arrow is right associative. So we can interpret an expression like ``f(a,b)`` implicitly as ``f(a)(b)``. In particular, we only need to support functions of one argument. But we also need to handle explicitly curried functions, like

    f(a)(b,c)

and we also need to allow arguments to be fenced in either parentheses or braces.

> fenced :: Parser a -> Parser a
> fenced p =
>       (between (char '(') (char ')') p)
>   <|> (between (char '{') (char '}') p)

We'll say that an "expression" is a constant or variable followed by zero or more fenced comma-delimited lists of subexpressions.

> pLatexExpr :: Parser Expr
> pLatexExpr = do
>   f <- pCon <|> pVar
>   args <- option [] $ many1 $ fenced $ sepBy1 pLatexExpr (char ',')
>   return $ foldl App f $ concat args

Nothing about the ``Expr`` type is specific to LaTeX, but (at least for now) this tool will be used specifically to parse and verify equations written in LaTeX.

While we're at it, some parsing helpers:

> parseWith :: String -> Parser a -> String -> Either String a
> parseWith loc p text = case runParser (p <* eof) () loc text of
>   Left err -> Left (show err)
>   Right x -> Right x
> 
> parseWithIO :: String -> Parser a -> String -> IO a
> parseWithIO loc p text = case parseWith loc p text of
>   Left msg -> putStrLn (unwords [loc,text,msg]) >> exitFailure
>   Right a  -> return a

And here is an example.

```haskell
$> x <- parseWithIO "" pLatexExpr "\\plus(a,\\times(b,c))"
$> putStrLn $ show x
App (App (Con "plus") (Var "a")) (App (App (Con "times") (Var "b")) (Var "c"))
```

We'll also make a function to pretty print ``Expr``s as LaTeX.

> latex :: Expr -> String
> latex (Con x) = '\\' : x
> latex (Var x) = x
> latex (App x y) = concat
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

Since lists are not actually maps, we need a helper function to decide whether a given list of token-expression pairs is well-defined. That is, a valid substitution shouldn't have two pairs with the same token but different expressions.

> wellDefined :: Substitution -> Bool
> wellDefined [] = True
> wellDefined ((x,a):ps) = and
>   [ null (filter (\(y,b) -> (x == y) && (a /= b)) ps)
>   , wellDefined ps
>   ]

Now actually making a substitution is straightforward; we march down an ``Expr``, and if we find a variable token replace it with its associated subexpression. We do the simplest thing by replacing _all_ instances of the variable.

> substitute :: Substitution -> Expr -> Expr
> substitute _ (Con a) =
>   Con a
> substitute es (Var x) =
>   case lookup x es of
>     Just e  -> e
>     Nothing -> Var x
> substitute es (App a b) =
>   App (substitute es a) (substitute es b)

Next we can try to construct a substitution taking one expression to another, based at the root. Constants match only themselves, variables match anything, and applications match recursively.

> matches :: Expr -> Expr -> Maybe Substitution
> matches pattern expr = match pattern expr >>= check
>   where
>     check ps = if wellDefined ps
>       then Just (nub ps)
>       else Nothing
> 
>     match (Con a) (Con b) =
>       if a == b then Just [] else Nothing
>     match (Con _) _ =
>       Nothing
>     match (Var x) e =
>       Just [(x,e)]
>     match (App e1 e2) (App f1 f2) = do
>       xs <- match e1 f1
>       ys <- match e2 f2
>       return (xs ++ ys)
>     match (App _ _) _ =
>       Nothing

More generally matches can occur anywhere in an expression, and we need to be able to unambiguously state where the match is. The ``Path`` type represents a series of directions for moving from the root of an expression to some interior node.

> data Path
>   = H | L Path | R Path
>   deriving (Eq, Show)

And ``matchesIn`` constructs a list of all substitutions from one expression to another, along with paths to the root of each substitution.

> matchesIn :: Expr -> Expr -> [(Path, Substitution)]
> matchesIn pattern expr = case expr of
>   Con a -> case matches pattern expr of
>     Nothing -> []
>     Just s  -> [(H, s)]
>   Var x -> case matches pattern expr of
>     Nothing -> []
>     Just s  -> [(H, s)]
>   App x y -> do
>     let
>       mx = map (\(p,z) -> (L p, z)) $ matchesIn pattern x
>       my = map (\(p,z) -> (R p, z)) $ matchesIn pattern y
>     case matches pattern expr of
>       Nothing -> mx ++ my
>       Just s  -> (H,s) : mx ++ my

Given a ``Path``, we can (attempt to) transform the subexpression it points to.

> transform :: (Expr -> Expr) -> Path -> Expr -> Maybe Expr
> transform f H expr = Just (f expr)
> transform f (L path) (App expr w) = do
>   q <- transform f path expr
>   Just (App q w)
> transform f (R path) (App w expr) = do
>   q <- transform f path expr
>   Just (App w q)
> transform _ _ _ = Nothing

As a special case, ``rewrite`` replaces the subexpression at a given location.

> rewrite :: Expr -> Path -> Expr -> Maybe Expr
> rewrite p = transform (const p)


Rewrite Rules
-------------

A *rewrite rule* is a pair of expressions that we interpret as being "equal" for all possible substitutions.

> type Rule = (Expr, Expr)

In our latexy syntax, we'll say a rewrite rule is two expressions, separated by an equals sign, and separated by spaces.

> pRule :: Parser Expr -> Parser Rule
> pRule p = do
>   a <- p
>   spaces
>   char '='
>   spaces
>   b <- p
>   return (a,b)

To apply a rewrite rule to an expression, we find all matches of the left hand side in the expression, substitute these into the right hand side, and then rewrite the expression.

> applyRule :: Rule -> Expr -> [Expr]
> applyRule (lhs,rhs) x =
>   catMaybes $ map applyMatch $ matchesIn lhs x
>   where
>     applyMatch (path,sub) = rewrite (substitute sub rhs) path x

To _validate_ a rule application -- to check that ``a = b`` maps ``e`` to ``f`` -- we apply the rule to ``e`` and see if ``f`` is among the resuls.

> validate :: Rule -> Expr -> Expr -> Bool
> validate rule input output = elem output (applyRule rule input)

Most of the rewrite rules and expressions we'll deal with are _symmetric_; we don't mind reversing the order of the expressions in the rewrite rule, and the roles of the input and output expressions. For this case we'll use a separate validation function.

> validateSymmetric :: Rule -> Expr -> Expr -> Bool
> validateSymmetric (lhs,rhs) e f = or
>   [ validate (lhs,rhs) e f
>   , validate (rhs,lhs) e f
>   , validate (lhs,rhs) f e
>   , validate (rhs,lhs) f e
>   ]


Interface
---------

Remember: this tool is specifically intended for use with the [Arithmetic Made Difficult](/pages/amd.html) posts, which include a few thousand lines worth of equational proofs. Those posts need two kinds of support.

1. We'd like to statically check the equalities in our equational proofs. Some equalities are annotated with a cross reference to the theorem that justifies them. Some `sed` magic can turn these into rewrite rules, which we can use to verify that the left hand side of an equality rewrites to the right hand side. Verifying one equality at a time, rather than an entire proof, makes it possible to build up static checks incrementally.
2. We'd also like to statically check variable substitutions. This is similar to scenario 1, except instead of rewriting a single (complex) subexpression, in this case we only care about replacing all instances of a variable with some expression and validating the result.
3. If an equality _doesn't_ have a cross referenced annotation, it'd be nice if our tool could also give suggestions for valid cross references based on a dictionary of rewrite rules. Bonus points if it also builds an edit script for inserting the annotation (hint, it will).

These requirements suggest that the tool needs three modes, which we'll call *verify* mode, *substitute* mode, and *suggest* mode, respectively.

We'll keep this really simple. In verify mode, the tool expects its input on `stdin`, one rewrite check per line, in the form

    location TAB rulelhs = rulerhs TAB from-expr TAB to-expr

Where `location` is some information about where the check comes from (for reporting problems). So we'll need to split a line on tabs:

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

And we'll need to process one untabbed line. We're assuming that the rewrite rules are symmetric; given `x = y` and two expressions `e` and `f`, any substitution taking either `e` to `f` or `f` to `e` is considered valid. This is ok for the equation chains we want to use this on.

> processVerify :: [String] -> IO ()
> processVerify [loc,r,a,b] = do
>   rule <- parseWithIO loc (pRule pLatexExpr) r
>   e <- parseWithIO loc pLatexExpr a
>   f <- parseWithIO loc pLatexExpr b
>   if validateSymmetric rule e f
>     then return ()
>     else putStrLn $ unwords [loc,"invalid!",r,"::",a,"-->",b]
> processVerify xs = do
>   putStrLn $ unwords ("unrecognized input format:" : xs)

In substitute mode, we'll accept input in the same format as for verify mode, with an extra check on the form of the rewrite rule.

> processSubstitute :: [String] -> IO ()
> processSubstitute [loc,r,a,b] = do
>   (lhs,rhs) <- parseWithIO loc (pRule pLatexExpr) r
>   e <- parseWithIO loc pLatexExpr a
>   f <- parseWithIO loc pLatexExpr b
>   case lhs of
>     Var x -> if (f == substitute [(x,rhs)] e) || (e == substitute [(x,rhs)] f)
>       then return ()
>       else putStrLn $ unwords [loc,"invalid!",r,"::",a,"-->",b]
>     _ -> do
>       putStrLn $ unwords [loc,"rewrite rule must be of the form 'var = expr':",r]
> processSubstitute xs = do
>   putStrLn $ unwords ("unrecognized input:" : xs)

In suggest mode, we'll assume that a dictionary of named rewrite rules is kept in some external file consisting of lines of the form

    name TAB rulelhs = rulerhs

> parseNamedRule :: [String] -> IO (String,(Expr,Expr))
> parseNamedRule [name,r] = do
>   (x,y) <- parseWithIO "-" (pRule pLatexExpr) r
>   return (name,(x,y))
> parseNamedRule xs = do
>   putStrLn $ unwords ("unrecognized input:":xs)
>   exitFailure

We'll also allow comment lines in the dictionary; these start with  a `#` character and are ignored.

> comment :: String -> Bool
> comment ('#':_) = True
> comment _ = False

We also assume backslashes are escaped in the dictionary because reasons.

> unesc :: String -> String
> unesc ('\\':'\\':xs) = '\\' : unesc xs
> unesc (c:cs) = c : unesc cs
> unesc [] = []

It will be more useful if in suggest mode, we ignore parse errors. Suggestion mode marches down the rules in the dictionary, and if it finds one, emits a `sed` command to insert an annotation. This part is completely ad-hoc.

> processSuggest :: [(String,(Expr,Expr))] -> [String] -> IO ()
> processSuggest ((name,(x,y)):rs) [loc,line,a,b] = do
>   lhs <- case parseWith loc pLatexExpr a of
>     Left _ -> return (Con "")
>     Right w -> return w
>   rhs <- case parseWith loc pLatexExpr b of
>     Left _ -> return (Con "")
>     Right w -> return w
>   if validateSymmetric (x,y) lhs rhs
>     then do
>       putStrLn $ unwords
>         [ "sed -i ''"
>         , "'"++line++"s/^ & = & / \\&     \\\\href{" ++ name ++ "}~   = \\& /'"
>         , loc
>         ]
>       else processSuggest rs [loc,line,a,b]
> processSuggest [] [_,_,_,_] = return ()
> processSuggest _ xs = do
>   putStrLn $ unwords xs

And `main`. In a departure from the unix philosophy, in verify mode we'll report the number of checks made.

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     ["--verify"] -> do
>       checks <- fmap (map unTab . lines) getContents
>       mapM_ processVerify checks
>       hPutStrLn stderr $ unwords [show $ length checks, "checks completed"]
> 
>     ["--substitute"] -> do
>       checks <- fmap (map unTab . lines) getContents
>       mapM_ processSubstitute checks
>       hPutStrLn stderr $ unwords [show $ length checks, "checks completed"]
> 
>     ["--suggest", path] -> do
>       rules <- (fmap (map unTab . filter (not . comment) . lines . unesc) $ readFile path)
>         >>= mapM parseNamedRule
>       checks <- fmap (map unTab . lines) getContents
>       putStrLn "#!/bin/bash"
>       mapM_ (processSuggest rules) checks
> 
>     _ -> do
>       putStrLn $ unlines
>         [ "usage:"
>         , "  --verify       : validate rewrites on stdin"
>         , "  --substitute   : validate substitutions on stdin"
>         , "  --suggest PATH : suggest rewrite rules from PATH on stdin"
>         ]


Testing
=======

The parts of this tool are complicated enough that I'll feel better having some tests.

> test_main :: IO ()
> test_main = do
>   parseSuccessTests
>   parseFailureTests
>   substituteTests
>   validationTests

Parsing tests helpers:

> testParseSuccess :: Int -> (String, Expr) -> IO ()
> testParseSuccess k (str,expr) = do
>   putStrLn $ "\nsuccess test " ++ show k
>   putStrLn str
>   case parseWith "" pLatexExpr str of
>     Left msg -> putStrLn msg >> exitFailure
>     Right ex -> if ex == expr
>       then putStrLn "ok"
>       else do
>         putStrLn $ unlines
>           [ "parse error:"
>           , str
>           , "expected: " ++ show expr
>           , "actual:   " ++ show ex
>           ]
>         exitFailure
> 
> testParseFailure :: Int -> String -> IO ()
> testParseFailure k str = do
>   putStrLn $ "\nfailure test " ++ show k
>   putStrLn str
>   case parseWith "" pLatexExpr str of
>     Right ex -> putStrLn (show ex) >> exitFailure
>     Left _   -> putStrLn "ok"

Parsing test cases:

> parseSuccessTests :: IO ()
> parseSuccessTests = sequence_ $ zipWith testParseSuccess [1..]
>   [ ("f", Var "f")
>   , ("\\f", Con "f")
>   , ("f(x)", App (Var "f") (Var "x"))
>   , ("\\f(x)", App (Con "f") (Var "x"))
>   , ("f(\\x)", App (Var "f") (Con "x"))
>   , ("\\f(\\x)", App (Con "f") (Con "x"))
>   , ("f{x}", App (Var "f") (Var "x"))
>   , ("\\f{x}", App (Con "f") (Var "x"))
>   , ("f{\\x}", App (Var "f") (Con "x"))
>   , ("\\f{\\x}", App (Con "f") (Con "x"))
>   , ("f(x,y)", App (App (Var "f") (Var "x")) (Var "y"))
>   , ("\\f(x,y)", App (App (Con "f") (Var "x")) (Var "y"))
>   , ("f(x)(y)", App (App (Var "f") (Var "x")) (Var "y"))
>   , ("f{x}(y)", App (App (Var "f") (Var "x")) (Var "y"))
>   , ("f(x,y)(z)", App (App (App (Var "f") (Var "x")) (Var "y")) (Var "z"))
>   , ("f(x)(y,z)", App (App (App (Var "f") (Var "x")) (Var "y")) (Var "z"))
>   , ("f{x,y}(z)", App (App (App (Var "f") (Var "x")) (Var "y")) (Var "z"))
>   , ("f{x}(y,z)", App (App (App (Var "f") (Var "x")) (Var "y")) (Var "z"))
>   , ("f(x)(g(y))", App (App (Var "f") (Var "x")) (App (Var "g") (Var "y")))
>   ]
> 
> parseFailureTests :: IO ()
> parseFailureTests = sequence_ $ zipWith testParseFailure [1..]
>   [ "#"
>   , "f(x"
>   , "f(x}"
>   , "\\fx)"
>   , "\\f(x,)"
>   , "\\f(,x)"
>   ]

Substitution test helper:

> testSubstitution :: Int -> (Substitution, Expr, Expr) -> IO ()
> testSubstitution k (sub,e1,e2) = do
>   putStrLn $ "\nsubstitution test " ++ show k
>   putStrLn $ show sub
>   putStrLn $ latex e1
>   if e2 == substitute sub e1
>     then putStrLn "ok"
>     else do
>       putStrLn $ unlines
>         [ "substitution error:"
>         , "expected: " ++ show e2
>         , "actual:   " ++ show (substitute sub e1)
>         ]
>       exitFailure

Substitution test cases:

> substituteTests :: IO ()
> substituteTests = sequence_ $ zipWith testSubstitution [1..]
>   [ ([], Con "a", Con "a")
>   , ([("a", Con "b")], Var "a", Con "b")
>   , ([("a", Con "b")], Con "a", Con "a")
>   , ([("a", App (Con "f") (Var "x"))], App (Con "g") (Var "a"), App (Con "g") (App (Con "f") (Var "x")))
>   , ([("a", Con "x")], App (Var "a") (Var "a"), App (Con "x") (Con "x"))
>   , ([("x", Var "y")], App (Var "x") (Var "x"), App (Var "y") (Var "y"))
>   , ([("x", Var "y")], App (Con "x") (Var "x"), App (Con "x") (Var "y"))
>   ]

Validation test helper:

> testValidate :: Int -> (Rule, Expr, Expr, Bool) -> IO ()
> testValidate k (rule,e1,e2,result) = do
>   putStrLn $ "\nvalidation test " ++ show k
>   putStrLn $ show rule
>   putStrLn $ latex e1
>   putStrLn $ latex e2
>   if result == validate rule e1 e2
>     then putStrLn "ok"
>     else do
>       putStrLn "validation error!"
>       exitFailure

Validation test cases:

> validationTests :: IO ()
> validationTests = sequence_ $ zipWith testValidate [1..]
>   [
>   ]
