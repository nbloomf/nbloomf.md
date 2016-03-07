---
title: site.lhs
---

It is traditional for sites built with Hakyll to provide the code used to generate them. I borrowed heavily from Hakyll's default example and from other sites to cobble this together; maybe someone else will find it useful.

**Frontmatter**

As usual we begin with some pragmas and imports. The OverloadedStrings pragma allows us to define globs as ordinary strings.

> {-# LANGUAGE OverloadedStrings #-}
> import Data.Monoid (mappend)
> import Hakyll
> import qualified Data.Set as S (insert)
> import Text.Pandoc.Options 
>   ( Extension(Ext_tex_math_dollars
>     , Ext_tex_math_double_backslash
>     , Ext_latex_macros)
>   , writerExtensions
>   , writerHTMLMathMethod
>   , HTMLMathMethod(MathJax) )

**The Main Function**

> main :: IO ()
> main = hakyll $ do
>   match "site.lhs" $ do
>     route   $ setExtension "html"
>     compile $ pandocCompiler
>       >>= loadAndApplyTemplate "templates/default.html" defaultContext
>       >>= relativizeUrls
>
>   match "LICENSE" $ do
>     route   idRoute
>     compile copyFileCompiler
>
>   match "raw/**" $ do
>     route   idRoute
>     compile copyFileCompiler
>
>   match "images/*" $ do
>     route   idRoute
>     compile copyFileCompiler
>
>   match "pdf/**" $ do
>     route   idRoute
>     compile copyFileCompiler
>
>   match "css/*" $ do
>     route   idRoute
>     compile compressCssCompiler
>
>   match (fromList ["about.md", "contact.md"]) $ do
>     route   $ setExtension "html"
>     compile $ pandocCompiler
>       >>= loadAndApplyTemplate
>             "templates/default.html" defaultContext
>       >>= relativizeUrls
>
>   match "classes/**" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate "templates/default.html" postCtx
>       >>= relativizeUrls
>
>   match "pages/sth/tool/*" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate
>             "templates/sth-tools.html" defaultContext
>       >>= loadAndApplyTemplate
>             "templates/default.html"   defaultContext
>       >>= relativizeUrls
>
>   match "pages/sth/index.md" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate "templates/default.html" postCtx
>       >>= relativizeUrls
>
>   match "posts/*" $ do
>     route $ setExtension "html"
>     compile $ pandocMathCompiler
>       >>= loadAndApplyTemplate "templates/macros.html"  postCtx
>       >>= loadAndApplyTemplate "templates/post.html"    postCtx
>       >>= loadAndApplyTemplate "templates/default.html" postCtx
>       >>= relativizeUrls
>
>   create ["archive.html"] $ do
>     route idRoute
>     compile $ do
>       posts <- recentFirst =<< loadAll "posts/*"
>       let archiveCtx =
>             listField "posts" postCtx (return posts) `mappend`
>             constField "title" "Archives"            `mappend`
>             defaultContext
>
>       makeItem ""
>         >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
>         >>= loadAndApplyTemplate "templates/default.html" archiveCtx
>         >>= relativizeUrls
>
>   match "index.md" $ do
>     route $ setExtension "html"
>     compile $ pandocCompiler
>       >>= loadAndApplyTemplate "templates/default.html" defaultContext
>       >>= relativizeUrls
>
>   match "templates/*" $ compile templateCompiler

**Compilers**

> postCtx :: Context String
> postCtx =
>   dateField "date" "%Y-%m-%d" `mappend`
>   defaultContext
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
>           foldr S.insert defaultExtensions mathExtensions
>       , writerHTMLMathMethod = MathJax ""
>       }
