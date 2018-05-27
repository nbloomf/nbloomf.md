---
title: Generating Images
author: nbloomf
date: 2018-04-14
tags: literate-haskell
---

I'm feeling bored today. Let's make some weird images!

> module GeneratingImages where

> import qualified Codec.Picture as JP
> import qualified Codec.Picture.Gif as JPG

So we can think of an image as a function from coordinates to colors -- where coordinates are just integers, and colors can be encoded as integers. For fun we can throw in animation too, and think of an image as a function from "frame number" and coordinate to color. So an image is "just" a function that takes three integers and returns an integer. Let's represent this with a type.

> data Img = Img (Int -> (Int, Int) -> Int)

Now the [JuicyPixels](https://hackage.haskell.org/package/JuicyPixels) library provides a bunch of functions for reading and writing images in different formats, which we can use to turn an `Img` into, say, a png.

> renderPng
>   :: FilePath
>   -> Img
>   -> Width
>   -> Height
>   -> IO ()
> 
> renderPng path (Img f) w h = do
>   let
>     png = JP.generateImage px w h
>     -- all components of the pixel are equal
>     px i j = JP.PixelRGB8 (cm i j) (cm i j) (cm i j)
>     -- clamp each component to the range [0..255]
>     cm i j = fromIntegral $ max 0 $ min 255 $ f 0 (i,j)
>   JP.savePngImage path (JP.ImageRGB8 png)

Where `Width` and `Height` are type aliases to make the signatures more clear.

> type Width = Int
> type Height = Int

Straight away we can use `renderPng` to visualize functions with signature `Int -> (Int, Int) -> Int`. For starters, here's the function that always returns 0.

> ex00 :: IO ()
> ex00 = do
>   let img = Img $ \_ _ -> 0
>   renderPng "raw/gfx/generate/ex00.png" img 256 256

![ex00](/raw/gfx/generate/ex00.png)

Woo! It's not very interesting! But we can do something a little more interesting. How about an image whose value is just its $x$-coordinate.

> x :: Img
> x = Img $ \_ (i,_) -> i

Let's see:

> ex01 :: IO ()
> ex01 = do
>   let img = x
>   renderPng "raw/gfx/generate/ex01.png" img 256 256

![$x$](/raw/gfx/generate/ex01.png)

That's... marginally less uninteresting. We can see how the color goes from black to white from left to right, since the value of the $x$-coordinate increases from 0. We can do the same with the $y$-coordinate.

> y :: Img
> y = Img $ \_ (_,j) -> j

Let's see:

> ex02 :: IO ()
> ex02 = do
>   let img = y
>   renderPng "raw/gfx/generate/ex02.png" img 256 256

![$y$](/raw/gfx/generate/ex02.png)

And we can also do the "frame" coordinate:

> f :: Img
> f = Img $ \f _ -> f

Which looks like this:

> ex03 :: IO ()
> ex03 = do
>   let img = f
>   renderPng "raw/gfx/generate/ex03.png" img 256 256

![$f$](/raw/gfx/generate/ex03.png)

That looks just like the constant 0 function! Which it is, since recall that `renderPng` evaluates its image at frame 0, so this _is_ just the constant 0 function. Sad! So `f` is boring for now, but it won't be for long.



Arithmetic
----------

Anyway, I have momentarily forgotten that our images are images, and have been thinking of them as just functions on the integers. And there's a natural way to lift the arithmetic on $\mathbb{Z}$ to the level of functions into $\mathbb{Z}$ -- by applying it pointwise.

Define some helpers like so:

> pointwise1 :: (Int -> Int) -> Img -> Img
> pointwise1 k (Img a) = Img $ \f (i,j) ->
>   k (a f (i,j))
> 
> pointwise2 :: (Int -> Int -> Int) -> Img -> Img -> Img
> pointwise2 k (Img a) (Img b) = Img $ \f (i,j) ->
>   k (a f (i,j)) (b f (i,j))

Now `Img` has an arithmetic (modeled in Haskell with the `Num` class).

> instance Num Img where
>   (+) = pointwise2 (+)
>   (*) = pointwise2 (*)
> 
>   fromInteger k = Img $ \_ _ -> fromIntegral k
> 
>   abs = pointwise1 abs
>   negate = pointwise1 negate
> 
>   signum = undefined

So we have a kind of arithmetic on images. Let's try it out. Here's $x + y$.

> ex04 :: IO ()
> ex04 = do
>   let img = x + y
>   renderPng "raw/gfx/generate/ex04.png" img 256 256

![$x+y$](/raw/gfx/generate/ex04.png)

And here's $xy$.

> ex05 :: IO ()
> ex05 = do
>   let img = x * y
>   renderPng "raw/gfx/generate/ex05.png" img 256 256

![$xy$](/raw/gfx/generate/ex05.png)

Okay. Not super interesting. Both $x+y$ and $xy$ have big flat white parts, which is kind of boring. The reason for this is that `renderPng` saturates at 255, meaning any values above that are clamped to 255. It would be nice if we could bring those larger values under control, to bring them within the visible range of $[0,255]$. But hey! We can! Two basic ways to make numbers smaller are _division_ and _remainder_.

Let's start with division. We define an operator on images like so.

> (//) :: Img -> Img -> Img
> (//) = pointwise2 div_
>   where
>     div_ :: Int -> Int -> Int
>     div_ a 0 = a
>     div_ a b = div a b

Note how we've defined division by 0, in violation of the laws of nature. Just be cool!

Anyway, let's try it out. On the interval $[0,255]$, the largest value $x+y$ takes on is $255+255 = 510$, which is larger than the maximum color value by a factor of 2.

> ex06 :: IO ()
> ex06 = do
>   let img = (x + y) // 2
>   renderPng "raw/gfx/generate/ex06.png" img 256 256

![$(x+y)/2$](/raw/gfx/generate/ex06.png)

Similarly, the largest value of $xy$ on $[0,255]$ is too large by a factor of about 256.

> ex07 :: IO ()
> ex07 = do
>   let img = (x * y) // 256
>   renderPng "raw/gfx/generate/ex07.png" img 256 256

![$(xy)/2$](/raw/gfx/generate/ex07.png)

Neat. The other operation for making big numbers small is _remainder_. We define remainder on images like so.

> (%) :: Img -> Img -> Img
> (%) = pointwise2 mod'
>   where
>     mod' :: Int -> Int -> Int
>     mod' a 0 = a
>     mod' a b = mod a b

Again note the definition of remainder mod 0. I argue that the undefinedness of `mod a 0` in Haskell is a bug, but whatever. Let's check it out. We can now make sure all parts of an image are "visible" -- meaning not saturated away -- by modding the image by 256. Here's what that looks like for $x+y$.

> ex08 :: IO ()
> ex08 = do
>   let img = (x + y) % 256
>   renderPng "raw/gfx/generate/ex08.png" img 256 256

![$x+y \pmod{256}$](/raw/gfx/generate/ex08.png)

Hmm, ok. That makes sense. Now for $xy$.

> ex09 :: IO ()
> ex09 = do
>   let img = (x * y) % 256
>   renderPng "raw/gfx/generate/ex09.png" img 256 256

![$xy \pmod{256}$](/raw/gfx/generate/ex09.png)

Much cooler!

Modding by 256 means we can visualize _any_ `Img`. Let's try a couple more... say some [2-forms](https://en.wikipedia.org/wiki/Homogeneous_polynomial).

> ex10 :: IO ()
> ex10 = do
>   let img = (x*x + y*y) % 256
>   renderPng "raw/gfx/generate/ex10.png" img 256 256

![$x^2 + y^2 \pmod{256}$](/raw/gfx/generate/ex10.png)

> ex11 :: IO ()
> ex11 = do
>   let img = (x*x - y*y) % 256
>   renderPng "raw/gfx/generate/ex11.png" img 256 256

![$x^2 - y^2 \pmod{256}$](/raw/gfx/generate/ex11.png)

> ex12 :: IO ()
> ex12 = do
>   let img = (x*x + x*y + y*y) % 256
>   renderPng "raw/gfx/generate/ex12.png" img 256 256

![$x^2 + xy + y^2 \pmod{256}$](/raw/gfx/generate/ex12.png)

> ex13 :: IO ()
> ex13 = do
>   let img = (x*x - x*y - y*y) % 256
>   renderPng "raw/gfx/generate/ex13.png" img 256 256

![$x^2 - xy - y^2 \pmod{256}$](/raw/gfx/generate/ex13.png)



Catenation
----------

> xcat :: Img -> Img -> Img -> Img
> xcat (Img m) (Img a) (Img b) = Img $ \f (i,j) ->
>   if i <= m f (i,j) then a f (i,j) else b f (i,j)
> 
> ycat :: Img -> Img -> Img -> Img
> ycat (Img m) (Img a) (Img b) = Img $ \f (i,j) ->
>   if j <= m f (i,j) then a f (i,j) else b f (i,j)
> 
> fcat :: Img -> Img -> Img -> Img
> fcat (Img m) (Img a) (Img b) = Img $ \f (i,j) ->
>   if f <= m f (i,j) then a f (i,j) else b f (i,j)

> mx :: Img -> Img -> Img
> mx = pointwise2 max

> ex14 :: IO ()
> ex14 = do
>   let img = cc 1 1 1 sharp ((x*x+y*y) %256)
>   renderPng "raw/gfx/generate/ex14.png" img 256 256

![$x^2 - xy - y^2 \pmod{256}$](/raw/gfx/generate/ex14.png)



Cross-Correlation
-----------------

> cc :: Int -> Int -> Int -> Img -> Img -> Img
> cc w h d (Img m) (Img a) = Img $ \f (i,j) ->
>   (sum [ (a f (i-u,j-v)) * (m f (u,v)) | u <- [(-w)..w], v <- [(-h)..h]]) `div` d

> mat :: Int -> Int -> [[Int]] -> Img
> mat w h css =
>   let
>     u = 2*w+1
>     v = 2*h+1
>   in
>     Img $ \_ (i,j) ->
>       if (abs i <= w) && (abs j <= h)
>         then (css !! (j+h)) !! (i+w)
>         else 0

> gblur3 :: Img
> gblur3 = mat 1 1 [[1,2,1],[2,4,2],[1,2,1]]

> edgeu :: Img
> edgeu = mat 1 1 [[1,1,1],[0,0,0],[0,0,0]]

> sharp :: Img
> sharp = mat 1 1 [[0,-1,0],[-1,5,-1],[0,-1,0]]



Animation
---------







 > ex14 :: IO ()
 > ex14 = do
 >   let img = (x*x + y*y - 8*f) % 256
 >   renderGif "raw/gfx/generate/ex14.gif" img 256 256 32 1

 ![$xy - y^2 \pmod{256}$](/raw/gfx/generate/ex14.gif)






> c :: Img -> (Img, Img) -> Img
> c (Img r) (Img u, Img v) = Img $ \f (i,j) ->
>   if (r f (i,j))^2 >= ((u f (i,j)) - i)^2 + ((v f (i,j)) - j)^2
>     then 1 else 0

> (@@) :: Img -> (Img, Img) -> Img
> (Img a) @@ (Img u, Img v) = Img $ \f (i,j) ->
>   a f (u f (i,j), v f (i,j))



> dx :: Img -> Img
> dx (Img a) = Img $ \f (i,j) ->
>   (a f (i,j)) - (a f (i-1,j))

> dy :: Img -> Img
> dy (Img a) = Img $ \f (i,j) ->
>   (a f (i,j)) - (a f (i,j-1))

> df :: Img -> Img
> df (Img a) = Img $ \f (i,j) ->
>   (a f (i,j)) - (a (f-1) (i,j))



> lg2' :: Int -> Int
> lg2' 0 = 0
> lg2' n = 1 + lg2' (n `div` 2)



> lg2 :: Img -> Img
> lg2 = pointwise1 lg2'



> renderGif :: FilePath -> Img -> Width -> Height -> Int -> Int -> IO ()
> renderGif path (Img f) w h num delay = do
>   let
>     cm k i j = fromIntegral $ max 0 $ min 255 $ f k (i,j)
>     img k = JP.generateImage (cm k) w h
>     frame k = (JPG.greyPalette, delay, img k)
>     frames = map frame [0..(num-1)]
>     result = JP.writeGifImages path JP.LoopingForever frames
>   case result of
>     Left err -> putStrLn $ "Error: " ++ err
>     Right it -> it

> renderPngC :: FilePath -> Img -> Img -> Img -> Width -> Height -> IO ()
> renderPngC path (Img r) (Img b) (Img g) w h = do
>   let
>     cm f i j = fromIntegral $ max 0 $ min 255 $ f 0 (i,j)
>     px i j = JP.PixelRGB8 (cm r i j) (cm b i j) (cm g i j)
>     png = JP.generateImage px w h
>   JP.savePngImage path (JP.ImageRGB8 png)



> main :: IO ()
> main = do
>  let f (k,x) = putStrLn (show k) >> x
>  mapM_ f $ zip [0..]
>   [ ex00, ex01, ex02, ex03, ex04, ex05, ex06, ex07, ex08, ex09
>   , ex10, ex11, ex12, ex13, ex14
>   ]

<style>
img { display: block; margin: 0 auto; }
figcaption { text-align: center; }
</style>
