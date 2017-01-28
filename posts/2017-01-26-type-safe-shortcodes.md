---
title: Type-safe shortcodes
author: nbloomf
date: 2017-01-26
tags: haskell
---

This is a story about how two different things I've been thinking about recently came together.

So lots of online services expose an embed API, right? These are special URLs that users can stick in an ``iframe`` to embed cat videos, say, into web pages. This is a handy way to [transclude](https://en.wikipedia.org/wiki/Transclusion) dynamic content in an otherwise static webpage. That is a nice thing about embed APIs.

One downside of embed APIs is that they can be cumbersome to use by hand; we have to remember the correct ``iframe`` attributes to set, and each embed API has its own fiddly knobs that can be tweaked, and all that has to be encoded in the embed URL in a way that's unique to each service. To get an idea for how this works, check out the [YouTube embed API](https://developers.google.com/youtube/player_parameters). Constructing a proper ``iframe`` isn't rocket science, but it's fiddly, and anything that's too fiddly won't get used as much as it could. This is a less nice thing about embed APIs.

WordPress has a nice feature for blog authors called *shortcodes*. WP shortcodes can do lots of things, but one of their main purposes is to make it easier to use embed APIs. It works like this: say I want to embed a YouTube video. We just take the URL and format it like so in our blog post:

```
[youtube https://www.youtube.com/watch?v=dQw4w9WgXcQ]
```

and WordPress will automagically reformat the URL as a proper ``iframe``; it even interprets the fiddly knobs in the URL for us. Very cool!

In my classes I sometimes use a tool called [GeoGebra](https://www.geogebra.org/) for demonstrations; it's open source point-and-click software for making and interacting with straightedge and compass constructions. GeoGebra has a web service for distributing and using demos. And it provides a nice embed API! Meaning that you can embed GeoGebra widgets in web pages if you want.

Well, I do want. Every GeoGebra widget has a unique ID code that is used to construct its embed URL. So I tried to implement a shortcode for WordPress so that users could type something like

```
[geogebra id="FOO"]
```

and have this automagically turned into the correct ``iframe``. Unfortunately, this didn't work out so well! It turns out that the shortcode handling code I wrote was badly vulnerable to [XSS attacks](https://en.wikipedia.org/wiki/Cross-site_scripting). Long story short, while the shortcode worked great when used as intended, things went pear-shaped if you tried to use it like this:

```
[geogebra id='" onload=launch_the_missiles() unused="']
```

Roughly speaking, my code would have allowed anyone to post a ``geogebra`` shortcode in the comments of any WordPress blog and run **arbitrary JavaScript**. That's game over, man. With arbitrary JavaScript you can emulate a frigging [Apple II](https://www.scullinsteel.com/apple2/). Malicious users can (and do) use XSS vulnerabilities less severe than this to their nefarious ends all the time.

To be clear, at no time did my vulnerable code come close to running on a real server. Fortunately this was caught very quickly by the WordPress maintainers, before it had a chance to do any damage. And I re-learned a lesson I've learned a hundred times before on the web: *trust nothing and no one*. :)

I was a little embarrassed to have missed what in hindsight should have been an obvious vulnerability. But I was also struck by how *easy* it was to write vulnerable code. The basic problem, I think, is that I made too many assumptions (the ``id`` parameter will be a valid ``id`` parameter) and tried to do the most obvious thing. But very often the most obvious thing is unsafe -- you have to go out of your way to keep bad things from happening. And this is too bad, because when code is not doing the most obvious thing it's much easier for buggy behaviour and broken edge cases to slip in.

But does it have to be this way? It would be nice if it were so easy to write safer code, or at least harder to write vulnerable code. At any rate, I had a real job to get back to, so I put this problem aside.


## Meanwhile...

In my day job as a teacher I have a new course this year that makes heavy use of YouTube videos. And rather than putting links to said videos on a web page, I decided I'd rather embed them.

The only issue with this idea was that this site (and all my course pages) are served statically from GitHub Pages rather than with WordPress. This site exists as a bunch of markdown-formatted files on my computer (and on [GitHub](https://github.com/nbloomf/nbloomf.md)) which gets "compiled" into proper HTML by a static site generator -- in this case, [Hakyll](https://jaspervdj.be/hakyll/). And yadda yadda yadda, no shortcodes. I can type out literal ``iframes`` like a hunter-gatherer, but that's no fun.

So why use a static site? As much as I love WordPress (and I do -- I have a reasonably trafficked WP blog floating around, which I tend not to emphasize my authorship of) I also like using the right tool for the job -- and for this particular site, the simplicity and extra security of static files outweighed the benefits of a dynamic site.

I chose Hakyll because it's small and lightweight and I like to play with Haskell. The bad news about Hakyll is that it's a niche player in a niche market -- a static site generator written in Haskell. As a result, the Hakyll user community is very small; so while even users of more popular SSGs have libraries of extensions written by other people to play with (like shortcodes!), in Hakyll land if you want something beyond the bare bones (like shortcodes!) you probably have to do it yourself. To some people this is fun. :)

At any rate, in the last couple of weeks, the following happened:

* I tried implementing a shortcode in PHP and fell into a very bad and very simple security trap.
* I found myself wanting to implement a shortcode extension for Hakyll.

And believe it or not these two scenarios were independent of each other. :) Only when I sat down to hack on Hakyll did it occur to me to apply the lessons of the first event to the second.


## Type Safety

To give away the punchline, I started building a shortcode extension for Hakyll called [hakyll-shortcode](https://github.com/nbloomf/hakyll-shortcode). It doesn't do too much yet -- it only understands a couple of shortcodes. It needs a test suite and better documentation, and could use a refactor. But the goal is to make it *hard* to write shortcodes that are vulnerable to malicious input.

And this is accomplished, in part, by using **type safety**.

I like to think of types in programming languages as colors. Every chunk of data has a color, and every function expects to get input data of specific colors. Some languages use only one color or a handful of barely distinguishable colors, while other languages differentiate colors by wavelength down to the nanometer.

Every language has a type model; some of them just don't do anything useful.

Just like a Phillips head screwdriver won't fit a slotted screw and a North American electrical cord won't plug into a European outlet, in a strictly typed programming language, trying to evaluate a function with inputs of the wrong color is an error. If your language is strictly typed enough, that error can be detected just by looking at the program's source and without having to run it. And if your language is *really* strictly typed, the compiler or interpreter can figure this out without you having to tell it the types of things all the time.

Haskell is *really* strictly typed.

What does this have to do with shortcodes and XSS attacks?

Let's think for a moment about exactly how shortcodes work. Say we've written our blog post and included a shortcode like this:

```
[youtube id="blah"]
```

Then to expand this shortcode we have to:

* Scan the text of the blog post looking for the shortcode string,
* Parse the shortcode string, and
* Replace the shortcode string with its ``iframe`` representation.

But in a really strictly typed language this isn't the whole story. In Haskell, for instance, the basic shape of the shortcode expansion procedure looks more like this:

* Scan the text of the blog post looking for the shortcode string,
* Parse the shortcode string **into an object of type ``t``**, and
* Replace the shortcode string with **the ``iframe`` representation of a type ``t`` object**.

The magic is in that type ``t``. Haskell is **really picky** about what kinds of things it considers ``t``s. But what is it? Well, an extremely simple form of the YouTube "shortcode type" might look something like this.

```haskell
data YouTubeEmbed = YouTubeEmbed
  { yt_id :: String
  }
```

If you're not familiar with Haskell, this is saying "a YouTubeEmbed object has a single property, ``yt_id``, which itself has type ``String``". And this is flawed, because in the absence of any explicit sanitization checks that string could be

```
" onload=launch_the_missiles() unused="
```

To prevent shenanigans, we need to restrict what characters can be in the ID of a YouTube embed. There's apparently no public documentation for this, but it appears that these IDs consist exclusively of alphanumeric characters with occasional hyphens and underscores.

So our shortcode type could just as easily look like this:

```haskell
data YouTubeEmbed = YouTubeEmbed
  { yt_id :: AlphanumericWithHyphensAndUnderscores
  }
```

where ``AlphanumericWithHyphensAndUnderscores`` is a not very creative name for the type of strings consisting only of alphanumeric characters, hyphens, and underscores. We can design the type so that we are barred from constructing values that do not satisfy that property. In this way, we can encode constraints on values in their types, and force our shortcode expander to only expand well typed shortcodes.

And here's the kicker -- Haskell is **so** strongly typed that this is basically all we have to do to make sure that ``yt_id`` only holds safe strings, because all data is immutable. By exposing the right API to shortcode authors, they/I can define new shortcodes by writing "obvious" things like

```haskell
data YouTubeEmbed = YouTubeEmbed
  { yt_id       :: AlphanumericWithHyphensAndUnderscores
  , yt_height   :: DecimalDigits
  , yt_width    :: DecimalDigits
  , yt_autoplay :: YesOrNo
  -- ...and so on
  }
```

and the type checker will not allow invalid embed objects to exist. Those details can happen behind the API, invisible to the shortcode implementer -- no explicit sanitization or validation required.

This moves the game from "check that we never output unsafe data" to "check that unsafe data is invalid" or equivalently "check that valid data is safe", which I claim (without proof) is easier.

I do not claim that these shortcodes are invulnerable to all possible attacks; such claims are always false. But using the type system to force shortcode data to have very specific colors helps eliminate a large class of errors.

## The End

The complete details are only a little more complicated; you can see the code on [GitHub](https://github.com/nbloomf/hakyll-shortcode) (it's a work in progress). By using GADTs, we can even provide an API so that the keys and allowed values of our shortcodes are described declaratively, sort of like the way the ``GetOpt`` library lets us declaratively define command line option parsers.

But shortcode implementers do not have to explicitly sanitize anything -- that is handled by the shortcode API and the type checker.

[geogebra id='QUUEPmCs']
