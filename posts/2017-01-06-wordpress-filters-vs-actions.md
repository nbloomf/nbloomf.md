---
title: WordPress: Filters vs. Actions
author: nbloomf
date: 2017-01-06
tags: wordpress
---

So I've been messing around with WordPress lately. It's this massively configurable CMS and blog engine written mostly in PHP. And the way you configure WP (for the most part) is using *hooks*, which come in two flavors: **filters** and **actions**. These two flavors appear to be very similar, but if we read the [documentation](https://codex.wordpress.org/Plugin_API) they are supposed to be used in very different ways.

I was puzzling over the difference between hooks and actions in WordPress when I realized that they make more sense if we imagine that PHP has types.

Using haskell-ish notation, filters have a type like this:

```haskell
filter :: b -> a -> a
```

while actions have a type like this:

```haskell
action :: b -> IO ()
```

Then after populating a named list of filters with ``filter1 b1``, ``filter2 b2``, et cetera, calling ``apply_filters`` does something like this:

```haskell
apply_filters :: a -> a
apply_filters a = filterN bN $ ... $ filter2 b2 $ filter1 b1 a
```

and after populating a named list of actions with ``action1 b1``, ``action2 b2``, et cetera, calling ``do_action`` does something like this:

```haskell
do_action :: IO ()
do_action = sequence_ [action1 b1, action2 b2, ..., actionN bN]
```

Of course PHP doesn't really have types, meaning that anything can change at any time for any reason (at least that's how I think about it -- I imagine that PHP takes place entirely in a special version of the ``IO`` monad that randomly triggers bugs). So *in practice* the programmer has to be disciplined enough to maintain the semantic difference between the two. But as I understand it these types capture the intended behavior.
