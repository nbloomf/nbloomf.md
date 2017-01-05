---
title: site.lhs
---

It is traditional for sites built with Hakyll to provide the code used to generate them: here is mine. I borrowed heavily from Hakyll's default example and from other sites to cobble this together; maybe someone else will find it useful.

This post is literate Haskell; code lines start with a ``>``, and all other lines (even lines that look like code!) are comments.

This file is not static and was not written all at once. Over time new bits get added and old bits get changed as my needs evolve.

**Frontmatter**

As usual we begin with some pragmas and imports, to be used later. The ``OverloadedStrings`` pragma allows us to define globs and filenames as ordinary strings; otherwise we'd be saying ``fromGlob`` everywhere.

> {-# LANGUAGE OverloadedStrings #-}
>
> module Main where
>
> import Hakyll
> import Data.Monoid (mconcat)
> import Data.Set (insert)
> import Text.Pandoc.Options 
>   ( Extension(Ext_tex_math_dollars
>     , Ext_tex_math_double_backslash
>     , Ext_latex_macros
>     )
>   , writerExtensions
>   , writerHTMLMathMethod
>   , HTMLMathMethod(MathJax)
>   )


**The Main Function**

Hakyll is a declarative DSL for building static websites. A typical Hakyll program is of the following form:
```haskell
main :: IO ()
main = hakyll rules

rules :: Rules ()
rules = undefined
```
where ``Rules`` is a special monad for turning source files into web pages. Come to think of it, Hakyll feels a lot like ``make``. The Hakyll docs typically define an element of ``Rules`` using one giant ``do`` block, maybe with smaller ``do`` blocks nested in it. I'm not a big fan of this style. Personally I prefer smaller functions with good names and explicit type signatures, so instead I will break up the rules into separate functions. Here's my ``main``:

> main :: IO ()
> main = hakyll $ do
>   matchRawFiles
>   matchCssFiles
>   matchLoneFiles
>   matchPosts
>   matchClasses
>   matchProjectPages
>   matchTemplates
>   createBlogArchive


**The Rules**

The ``matchRawFiles`` rule handles files that should be copied verbatim, with no extra processing.

> matchRawFiles :: Rules ()
> matchRawFiles = match
>   ("LICENSE" .||. "raw/**" .||. "images/**" .||. "pdf/**") $
>   route idRoute >> compile copyFileCompiler

The ``matchCssFiles`` rule is almost identical to ``matchRawFiles``; this time we use the Hakyll function ``compressCssCompiler``, which minifies CSS. It looks like this compiler just removes extra whitespace and newlines.

> matchCssFiles :: Rules ()
> matchCssFiles = match "css/*" $
>   route idRoute >> compile compressCssCompiler

The ``matchLoneFiles`` rule handles standalone pages, like ``about`` and ``contact``. The easiest way to add a new page (not a post) is to add it to the list of names handled by ``mathcLoneFiles``.

> matchLoneFiles :: Rules ()
> matchLoneFiles = match names $ do
>   route $ setExtension "html"
>   compile $ pandocMathCompiler
>     >>= loadAndApplyTemplate
>           "templates/default.html" postCtx
>     >>= relativizeUrls
>
>   where
>     names = fromList
>       [ "site.lhs"
>       , "index.md"
>       , "about.md"
>       , "contact.md"
>       , "projects.md"
>       , "pages/sth/index.md"
>       , "pages/sth/formats.md"
>       , "pages/amd/index.md"
>       , "pages/alg-notes.md"
>       , "pages/geo-notes.md"
>       ]

The ``matchPosts`` rule is a little different from the others we've seen so far. It handles blog posts. But instead of listing out the source files by name, we capture them in a glob: ``"posts/*"``. These work similarly to shell globs but (as usual) have their own quirks; see the [documentation](https://jaspervdj.be/hakyll/reference/Hakyll-Core-Identifier-Pattern.html) for details.

> matchPosts :: Rules ()
> matchPosts = do
>   tags <- buildTags "posts/*" (fromCapture "tag/*.html")
>
>   match "posts/*" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate
>             "templates/post.html" (postWithTagsCtx tags)
>       >>= loadAndApplyTemplate
>             "templates/default.html" (postWithTagsCtx tags)
>       >>= relativizeUrls
>
>   tagsRules tags $ \tag pattern -> do
>     let title = "Posts tagged \"" ++ tag ++ "\""
>     route idRoute
>     compile $ do
>       posts <- recentFirst =<< loadAll pattern
>
>       let ctx = mconcat
>             [ constField "title" title
>             , listField "posts" postCtx (return posts)
>             , defaultContext
>             ]
>
>       makeItem ""
>         >>= loadAndApplyTemplate "templates/tag.html" ctx
>         >>= loadAndApplyTemplate "templates/default.html" ctx
>         >>= relativizeUrls

The ``matchClasses`` rule is similar to ``matchPosts``; it handles the source files for my course pages.

> matchClasses :: Rules ()
> matchClasses = match "classes/**" $ do
>   route $ setExtension "html"
>   compile $ pandocMathCompiler
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
>
>   match "pages/amd/sec/*" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate
>             "templates/amd-sec.html" defaultContext
>       >>= loadAndApplyTemplate
>             "templates/default.html" defaultContext
>       >>= relativizeUrls

The ``matchTemplates`` rule simply loads our HTML templates for use by Hakyll (I think).

> matchTemplates = match "templates/*" $
>   compile templateCompiler

The ``createBlogArchive`` rule is different from the others as it generates a new file, rather than simply transforming an existing file.

> createBlogArchive :: Rules ()
> createBlogArchive = create ["archive.html"] $ do
>   route idRoute
>   compile $ do
>     posts <- recentFirst =<< loadAll "posts/*"
>
>     let archiveCtx = mconcat
>           [ listField "posts" postCtx (return posts)
>           , constField "title" "Archives"
>           , defaultContext
>           ]
>
>     makeItem ""
>       >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
>       >>= loadAndApplyTemplate "templates/default.html" archiveCtx
>       >>= relativizeUrls


**Compilers**

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
> pandocMathCompiler = pandocCompilerWith defaultHakyllReaderOptions opts
>   where
>     mathExtensions = 
>       [ Ext_tex_math_dollars
>       , Ext_tex_math_double_backslash
>       , Ext_latex_macros
>       ]
>
>     defaultExtensions = writerExtensions defaultHakyllWriterOptions
>
>     opts = defaultHakyllWriterOptions 
>       { writerExtensions =
>           foldr insert defaultExtensions mathExtensions
>       , writerHTMLMathMethod = MathJax ""
>       }
