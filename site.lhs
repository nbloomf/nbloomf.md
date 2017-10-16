---
title: site.lhs
---

It is traditional for sites built with Hakyll to provide the code used to generate them: here is mine. I borrowed heavily from Hakyll's default example and from other sites to cobble this together; maybe someone else will find it useful.

This post is literate Haskell; code lines start with a ``>``, and all other lines (even lines that look like code!) are comments.

This file is not static and was not written all at once. Over time new bits get added and old bits get changed as my needs evolve.


Frontmatter
-----------

As usual we begin with some pragmas and imports, to be used later. The ``OverloadedStrings`` pragma allows us to define globs and filenames as ordinary strings; otherwise we'd be saying ``fromGlob`` everywhere.

> {-# LANGUAGE OverloadedStrings #-}
>
> module Main where
>
> import Hakyll
> import Hakyll.Shortcode
> import Control.Monad
> import Data.Monoid (mconcat)
> import qualified Data.Set as S (fromList, union)
> import Text.Regex (subRegex, mkRegex)
> import Text.Pandoc.Options 
>   ( Extension(..)
>   , writerExtensions
>   , writerHTMLMathMethod
>   , HTMLMathMethod(MathJax)
>   )


The Main Function
-----------------

Hakyll is a declarative DSL for building static websites. A typical Hakyll program is of the following form:
```haskell
main :: IO ()
main = hakyllWith rules

rules :: Rules ()
rules = undefined
```
where ``Rules`` is a special monad for turning source files into web pages. Come to think of it, Hakyll feels a lot like ``make``. The examples in the Hakyll docs typically define an element of ``Rules`` using one giant ``do`` block, maybe with smaller ``do`` blocks nested in it. I'm not a big fan of this style. Personally I prefer smaller functions with good names and explicit type signatures, so instead I will break up the rules into separate functions. Here's my ``main``:

> main :: IO ()
> main = hakyllWith config $ do
>   matchRawFiles
>   matchCssFiles
>   matchLoneFiles
>   matchPages
>   matchClasses
>   matchProjectPages
>   matchTemplates
>   createBlogArchive
>   create404
>
>   tags <- buildTags "posts/**" (fromCapture "tag/*.html")
>   matchPosts tags
>   createTagPages tags
> 
> 
> config :: Configuration
> config = defaultConfiguration
>   { previewPort = 31337
>   }


The Rules
---------

The ``matchRawFiles`` rule handles files that should be copied verbatim, with no extra processing.

> matchRawFiles :: Rules ()
> matchRawFiles =
>   let
>     raw = anyPattern
>       [ "LICENSE"
>       , "raw/**"
>       , "pdf/**"
>       ]
>   in
>     match raw $
>       route idRoute >> compile copyFileCompiler

The ``matchCssFiles`` rule is almost identical to ``matchRawFiles``; this time we use the Hakyll function ``compressCssCompiler``, which minifies CSS. It looks like this compiler just removes extra whitespace and newlines.

> matchCssFiles :: Rules ()
> matchCssFiles = match "css/*" $
>   route idRoute >> compile compressCssCompiler

The ``matchLoneFiles`` rule handles standalone pages, like ``about`` and ``contact``. The easiest way to add a new page (not a post) is to add it to the list of names handled by ``matchLoneFiles``.

> matchLoneFiles :: Rules ()
> matchLoneFiles =
>   let
>     names = fromList
>       [ "site.lhs", "index.md" ]
>   in
>     match names $ do
>       route $ setExtension "html"
>       compile $ pandocMathCompiler
>         >>= applyShortcodes allServices
>         >>= loadAndApplyTemplate
>               "templates/default.html" postCtx
>         >>= relativizeUrls

> matchPages :: Rules ()
> matchPages = do
>   match "pages/**" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate
>             "templates/default.html" postCtx
>       >>= relativizeUrls

The ``matchPosts`` rule is a little different from the others we've seen so far. It handles blog posts. But instead of listing out the source files by name, we capture them in a glob: ``"posts/*"``. These work similarly to shell globs but (as usual) have their own quirks; see the [documentation](https://jaspervdj.be/hakyll/reference/Hakyll-Core-Identifier-Pattern.html) for details.

> matchPosts :: Tags -> Rules ()
> matchPosts tags = do
>   match (anyPattern ["posts/**.md", "posts/**.lhs"]) $ do
>     route $ setExtension "html"
>
>     let ctx = postWithTagsCtx tags
>
>     compile $ pandocMathCompiler
>       >>= applyShortcodes allServices
>       >>= applyTagTemplates ctx
>             [ ("literate-haskell",
>                 "templates/literate-haskell.html")
>             , ("software-tools-in-haskell",
>                 "templates/sth-tools.html")
>             , ("arithmetic-made-difficult",
>                 "templates/amd.html")
>             , ("project-euler",
>                 "templates/project-euler-solutions.html")
>             , ("ml",
>                 "templates/ml.html")
>             ]
>       >>= loadAndApplyTemplate
>             "templates/post.html" ctx
>       >>= loadAndApplyTemplate
>             "templates/default.html" ctx
>       >>= relativizeUrls

Here we also used a custom compiler, ``applyTagTemplate``, which loads a given template only if a post has a given tag. This is a cheap way to give some and only some posts a custom header or style.

> applyTagTemplates ctx ts x =
>   let foo z (tag,temp) = applyTagTemplate tag temp ctx z
>   in foldM foo x ts
> 
> 
> applyTagTemplate tag template context x = do
>   path <- getUnderlying
>   tags <- getTags path
>   if elem tag tags
>     then loadAndApplyTemplate template context x
>     else return x

We also apply a custom filter for converting "shortcodes" (borrowing a WordPress term) into ``iframes``. This is inspired by code shamelessly cribbed from [Jonas Hietala](http://www.jonashietala.se/blog/2014/09/01/embedding_youtube_videos_with_hakyll/) ([archive](http://web.archive.org/web/20161005181904/http://www.jonashietala.se/blog/2014/09/01/embedding_youtube_videos_with_hakyll/)), but the guts are in a separate library, [``hakyll-shortcode``](https://github.com/nbloomf/hakyll-shortcode).

The ``matchClasses`` rule is similar to ``matchPosts``; it handles the source files for my course pages.

> matchClasses :: Rules ()
> matchClasses = match "classes/**" $ do
>   route $ setExtension "html"
>   compile $ pandocMathCompiler
>     >>= applyShortcodes allServices
>     >>= loadAndApplyTemplate
>           "templates/default.html" postCtx
>     >>= relativizeUrls

The ``matchProjectPages`` rule is also similar to ``matchPosts``; these rules are separated so we can use custom templates.

> matchProjectPages :: Rules ()
> matchProjectPages = do
>   match "pages/sth/tool/*" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate
>             "templates/sth-tools.html" defaultContext
>       >>= loadAndApplyTemplate
>             "templates/default.html"   defaultContext
>       >>= relativizeUrls

The ``matchTemplates`` rule simply loads our HTML templates for use by Hakyll (I think).

> matchTemplates = match "templates/**" $
>   compile templateCompiler

The ``createBlogArchive`` rule is different from the others as it generates a new file, rather than simply transforming an existing file.

> createBlogArchive :: Rules ()
> createBlogArchive = create ["archive.html"] $ do
>   route idRoute
>   compile $ do
>     posts <- recentFirst =<< loadAll "posts/**"
>
>     let
>       archiveCtx = mconcat
>         [ listField "posts" postCtx (return posts)
>         , constField "title" "Archives"
>         , defaultContext
>         ]
>
>     makeItem ""
>       >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
>       >>= loadAndApplyTemplate "templates/default.html" archiveCtx
>       >>= relativizeUrls

Custom 404 page for broken links.

> create404 :: Rules ()
> create404 = create ["404.html"] $ do
>   route idRoute
>   compile $ do
>     let
>       ctx = mconcat
>         [ constField "title" "404 - Not Found"
>         , constField "body" $ concat
>             [ "<div class='four-oh-four'>"
>             , "You step in the stream,<br />"
>             , "But the water has moved on.<br />"
>             , "This page is not here."
>             , "</div>"
>             ]
>         , defaultContext
>         ]
>
>     makeItem ""
>       >>= loadAndApplyTemplate "templates/default.html" ctx

The ``createTagPages`` rule generates a bunch of pages for each tag, and an index of all tags. Woo!

> createTagPages :: Tags -> Rules ()
> createTagPages tags = do
>   tagsRules tags $ \tag pattern -> do
>     let title = "Posts tagged \"" ++ tag ++ "\""
>     route idRoute
>     compile $ do
>       posts <- recentFirst =<< loadAll pattern
>
>       let
>         ctx = mconcat
>           [ constField "title" title
>           , listField "posts" postCtx (return posts)
>           , defaultContext
>           ]
>
>       makeItem ""
>         >>= loadAndApplyTemplate "templates/tag.html" ctx
>         >>= loadAndApplyTemplate "templates/default.html" ctx
>         >>= relativizeUrls
>
>   create ["tags/index.html"] $ do
>     route idRoute
>     compile $ do
>
>       let
>         ctx = mconcat
>           [ constField "title" "Tags" 
>           , defaultContext
>           ]
>
>       renderTagList tags
>         >>= makeItem
>         >>= loadAndApplyTemplate "templates/default.html" ctx
>         >>= relativizeUrls


Compilers
---------

> postCtx :: Context String
> postCtx = mconcat
>   [ dateField "date" "%Y-%m-%d"
>   , defaultContext
>   ]
>
> postWithTagsCtx :: Tags -> Context String
> postWithTagsCtx tags = mconcat
>   [ tagsField "tags" tags
>   , postCtx
>   ]
>
> pandocMathCompiler :: Compiler (Item String)
> pandocMathCompiler = pandocCompilerWith defaultHakyllReaderOptions customWriterOptions
>   where
>     customWriterOptions = defaultHakyllWriterOptions 
>       { writerExtensions = S.union
>           (writerExtensions defaultHakyllWriterOptions)
>           (S.fromList
>              [ Ext_tex_math_dollars
>              , Ext_tex_math_double_backslash
>              , Ext_latex_macros
>              , Ext_grid_tables
>              ])
>
>       , writerHTMLMathMethod = MathJax ""
>       }


Helpers
-------

> anyPattern :: [Pattern] -> Pattern
> anyPattern = foldl1 (.||.)

