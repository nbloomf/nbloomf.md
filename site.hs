--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import Data.Monoid (mappend)
import Hakyll
import qualified Data.Set as S (insert)
import Text.Pandoc.Options 
  ( Extension(Ext_tex_math_dollars
    , Ext_tex_math_double_backslash
    , Ext_latex_macros)
  , writerExtensions
  , writerHTMLMathMethod
  , HTMLMathMethod(MathJax) )
--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
  match "LICENSE" $ do
    route   idRoute
    compile copyFileCompiler

  match "images/*" $ do
    route   idRoute
    compile copyFileCompiler

  match "pdf/*" $ do
    route   idRoute
    compile copyFileCompiler

  match "css/*" $ do
    route   idRoute
    compile compressCssCompiler

  match (fromList ["about.md", "contact.md"]) $ do
    route   $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/default.html" defaultContext
      >>= relativizeUrls

  match "classes/**" $ do
    route $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/default.html" postCtx
      >>= relativizeUrls

  match "posts/*" $ do
    route $ setExtension "html"
    compile $ pandocMathCompiler
      >>= loadAndApplyTemplate "templates/macros.html"  postCtx
      >>= loadAndApplyTemplate "templates/post.html"    postCtx
      >>= loadAndApplyTemplate "templates/default.html" postCtx
      >>= relativizeUrls

  create ["archive.html"] $ do
    route idRoute
    compile $ do
      posts <- recentFirst =<< loadAll "posts/*"
      let archiveCtx =
            listField "posts" postCtx (return posts) `mappend`
            constField "title" "Archives"            `mappend`
            defaultContext

      makeItem ""
        >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
        >>= loadAndApplyTemplate "templates/default.html" archiveCtx
        >>= relativizeUrls


  match "index.md" $ do
    route $ setExtension "html"
    compile $ pandocCompiler
      >>= loadAndApplyTemplate "templates/default.html" defaultContext
      >>= relativizeUrls

  match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
  dateField "date" "%B %e, %Y" `mappend`
  defaultContext

pandocMathCompiler :: Compiler (Item String)
pandocMathCompiler = pandocCompilerWith defaultHakyllReaderOptions writerOpts
  where
    mathExtensions = 
      [Ext_tex_math_dollars, Ext_tex_math_double_backslash, Ext_latex_macros]

    defaultExtensions = writerExtensions defaultHakyllWriterOptions

    writerOpts = defaultHakyllWriterOptions 
      { writerExtensions = foldr S.insert defaultExtensions mathExtensions
      , writerHTMLMathMethod = MathJax "" }
