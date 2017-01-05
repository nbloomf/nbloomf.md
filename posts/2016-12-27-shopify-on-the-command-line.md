---
title: Shopify on the command line
author: nbloomf
date: 2016-12-27
tags: shopify, unix, cli
---

This post is about how you can edit a Shopify shop from the command line. It's also a little long! I will assume you know what Shopify is and the basics of shell scripting, and that you have a unix-like environment (Linux, BSD, macOS), but otherwise have no special knowledge of the guts of Shopify or HTTP-based APIs, just like me when I started this.

Today we will be adding a ``rel="nofollow"`` attribute to all the links on a shop blog, but the techniques can be used to make many different kinds of changes.

Along the way we'll be using some old workhorses: ``sed``, ``grep``, and ``wget``. We will also use some tools that might not have come with your OS: ``curl``, ``jq``, and the ``html-xml-utils``. These are all free software and probably available for your system.

**Disclaimer:** This post includes shell commands which you can copy and run on your own machine, including some which will destructively edit data. You should never run random shell commands from the internet without understanding what they do. I will explain what's going on, but before trying this yourself *back up* any data that you don't want to lose! (We'll talk about how to do that.)


## The Setup

This story requires a little bit of prologue.

My partner Stacie has been running an online shop called [Gingiber](http://gingiber.com) for several years now. She started out selling on [Etsy](https://www.etsy.com/shop/Gingiber) and blogging on Blogger, but a couple of years ago expanded to the [Shopify](http://gingiber.com) platform, which integrates ecommerce and very simple blogging tools. (All things being equal I would much rather use [WordPress](http://wordpress.org) for the blog, but we have to stick with Shopify's blog because reasons.) The old blog posts included announcements, interviews with artists, home projects, music reviews, product giveaways, and more. Stacie hired a designer to build the Shopify site; they also imported all her old blog posts to the new platform and all was well.

Until a few weeks ago! We got an email from Google saying that due to a pattern of  "unnatural, artificial, deceptive, or manipulative outbound links" the Gingiber shop would be penalized in Google's search rankings. (Apparently this is [A Thing](https://www.google.com/search?&q=%22unnatural+outbound+link%22+manual+action) that started happening this year.) An included note said that some links appear to be paid advertisements attempting to pass PageRank. Uh oh! Gingiber doesn't get a ton of traffic from search engines, but it does get some. And being actively penalized means it won't get more. So we've got a strong incentive to fix the problem.

To be clear, there aren't any paid/traded/otherwise-compensated links on the blog. But that doesn't matter. If the robots at Google decide that a link looks deceptive, then it is, full stop. The only thing we can do is make the changes Google wants and hope the robots become happy again.

So what's the fix? The bad links need either (1) to be removed or (2) to have a ``rel="nofollow"`` attribute, which Google uses as a signal that a link should not pass PageRank. Since (1) is not really an option, we'll go with (2).

And which links are bad? Google can't tell us, because if they go around saying "we think this looks bad because X" then actual scammers will just route around X. But given that none of the links are actually made in exchange or as part of a shady scheme, we have no way of knowing which ones need to be fixed. So it looks like the simplest thing to do is just make *all* outbound links ``nofollow``, and maybe later whitelist some.

Anyway, this is not a post about SEO, or to complain about Google. :) It's a post about a technical solution to the following specific problem:

> What is the easiest and fastest way to add a ``rel="nofollow"`` attribute to all ~4000 of the links on my Shopify blog?


## How To Edit A Blog Post

I pulled a fast one in that problem statement above by asking to optimize two different things: easiness and fastness. The *easiest* thing to do is go into Shopify's [blog editing interface](https://help.shopify.com/manual/sell-online/online-store/blogs/writing-blogs), open each post, view in source mode, and manually add ``rel="nofollow"`` to each ``<a>`` tag. It takes a couple dozen clicks per post, but that's easy.

It's also *slooooow*.

There's several hundred posts to look at, each with multiple links. Surely there must be a less manual way to edit blog posts. And there is! Shopify provides a REST API over HTTP that can edit just about anything we want. To see how, let's unpack those acronyms.

Basically, Shopify keeps all our data hidden somewhere -- maybe in a database, maybe etched into stone tablets, I don't know. The only way to interact with that data is with HTTP requests. Usually this is handled by your web browser. Firefox, for example, will take a URL like ``https://gingiber.com/collections/cards`` and turn it into an HTTP ``GET`` request which is sent to Shopify's server. The server responds, in this case, by sending back an HTML file.

But there are some other HTTP requests that, instead of getting data, and as long as the server knows what to do with them, can write new data (``POST``), or update existing data (``PUT``). (There are other kinds of requests too, but we don't need them right now.)

Shopify helpfully provides very thorough [documentation](https://help.shopify.com/api/reference) of exactly what you can do with HTTP requests. This is called an *API*, or [Application Programming Interface](https://en.wikipedia.org/wiki/Application_programming_interface). More precisely it is a *REST* API (REpresentational State Transfer), meaning (in a nutshell) that individual requests represent independent, atomic edits to our hidden Shopify data.

Different URL paths are called *endpoints* and do different things. Most important for us are these two:

1. ``GET /admin/blogs/{blog-id}/articles/{article-id}.json``
2. ``PUT /admin/blogs/{blog-id}/articles/{article-id}.json``

The first kind of request gets a particular blog post, structured in JSON format. The second kind of request takes similarly structured JSON data and uses it to update an existing post. Essentially, we can ``GET`` a post, edit it on our local machine using whatever tools we want, and then ``PUT`` it back. All we need to know is the ID number of our blog and the ID number of the post we want to edit. (We'll see how to find these in a minute.)

There is one catch: if we want to interact with our shop using the API, it's not enough just to know which URLs to send requests to. We also need to have *permission* to interact with our shop using the API. Otherwise, anyone could edit any shop -- big problem! Luckily, getting permission to edit your own shop is not hard. You need 3 things:

1. Your shop's domain (the part of the URL between ``https://`` and the next ``/``),
2. A private API key (which is really just a kind of username), and
3. A password.

You should know your domain; it's the URL on your business cards. :) And getting a private API key and password is easy; just follow the [directions](https://help.shopify.com/api/guides/api-credentials#generate-private-app-credentials) from Shopify. (Note that to follow along here, you only need a *private* key, not a *public* one, which is good, because private credentials are a bit easier to use.) **You should never tell anyone what your credentials are.** Anyone who has your API key and password can wreak havoc upon your shop. So be cool! Also, you can revoke (delete) a set of credentials at any time and create a new one, and doing so is not a bad idea.

With your key, password, and domain in hand, the simplest way to use the API is to send requests to ``https://{api-key}:{password}@{domain}/{endpoint}``. (Note the use of ``https``; this is important.) We can make these requests in the command line with ``curl``, like this example which uses the ``/admin/blogs.json`` endpoint:

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs.json"
```

You can copy this command directly in your shell or put it in a shell script (``#!/bin/bash``, then ``chmod +x``), just remember to substitute your own API key, password, and domain. BUT DON'T RUN IT YET! First, let's think about what this command *should* do.

[``curl``](https://curl.haxx.se/) is a mature and powerful tool for working with URLs from the command line; by giving it a URL starting with ``http`` it sends HTTP requests. The ``-X`` option specifies the request method; it's redundant here, because ``GET`` is the default, but I prefer to be explicit since we'll be using other methods later.

According to the [documentation](https://help.shopify.com/api/reference/blog#index) for this endpoint, the response to this request should be a list of all the blogs associated to your shop. This list will be encoded using [JSON](https://en.wikipedia.org/wiki/JSON). (OK, try running the command now.)

Hopefully that worked! I will continue as if it did. :) Each item in the returned list includes a bunch of information, like the ID of the blog (we need that for later!) and all the tags used on any posts. Depending on how big your blog/s is/are, you may get a bunch of stuff back; for instance, the blog I'm working with has a couple hundred tags. Right now I just want to get the ID of our blog. We can extract this from the JSON response by piping into ``jq`` like so:

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs.json" \
  | jq '.blogs[] | {id: .id, title: .title}'
```

``jq`` is a tool for munging JSON on the command line. That last argument string tells ``jq`` how to deconstruct its input JSON and build it into new JSON; in this case, we take each item in the ``blogs`` array and extract its ``id`` and ``title``. This tool has its own little expression language for building queries and the [``jq`` documentation](https://stedolan.github.io/jq/manual/) is pretty good.

Anyway, that last command should result in something like this:

```json
{
  "id": 1234567,
  "title": "Blog Title"
}
```

where ``1234567`` is the ID number of your blog. If you have more than one blog, all of their IDs will be listed here. **Remember the ID of the blog you want to edit.**

Neat! With ``curl``, ``jq``, and the right endpoint, we can get information about our shop delivered to our command line. At this point you could play around with different endpoints to see what they do. But we've got a job to do, so let's try it again, this time to see a count of how many articles our blog has.

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs/{blog-id}/articles/count.json"
```

I'm skipping ``jq`` this time because the output is so small -- just one numeric field. My output looks like this:

```json
{"count":697}
```

Remember that in order to GET a post, edit it, and PUT it back, we're going to need the ID of our blog (got that) as well as the IDs of all our posts. But there's no endpoint in the API that gives all the post IDs directly. There is, however, an endpoint that gives us lists of posts: [``/admin/blogs/{blog-id}/articles.json``](https://help.shopify.com/api/reference/article#index). This endpoint even takes some parameters: importantly for us, ``fields``, ``limit``, and ``since_id``.

Shopify limits the amount of information you can get with any one request. For example, using this endpoint to get a list of articles will not return *all* of the articles, but only the first 50. To get the rest we have to use parameters. The ``limit`` parameter lets us get up to 250 articles at once, instead of 50. The ``since_id`` lets us set our own lower bound on the numeric IDs of the articles to be retrieved -- the default is effectively 0. And the ``fields`` parameter lets us filter out only the info we want. ``jq`` can do this too, but by using the ``fields`` parameter that filtering can happen before our response hits the wire, rather than after, for a very slight performance boost.

For example, the following command gives us a list of the first 250 article IDs.

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs/{blog-id}/articles.json?fields=id&limit=250&since_id=0" \
  | jq '.articles[] | .id'
```

Save that list somewhere (pipe it to a file). Note the largest ID, and use that value to replace the ``0`` in ``since_id=0`` to get the next 250 article IDs. Repeat this until you catch 'em all.

If your blog is really big, you could wrap this step in a shell script to get all the IDs in one go. Mine is small enough that it was easier to do this by hand.

If you saved the article IDs in ``ids.txt``, you can verify that the list is complete like this:

```bash
cat ids.txt | sort | uniq | wc --lines
```

This should agree with the article count reported by the ``count`` endpoint.

Alright: by now you should have the following:

1. An API key and password for using the Shopify API,
2. The ID number of the blog you want to edit, and
3. The ID numbers of all the articles on the blog from 2.

Onward!


## Editing posts, for real

Now let's get the contents of a single blog post; the ``/admin/blogs/{blog-id}/articles/{article-id}.json`` endpoint can do that.

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs/{blog-id}/articles/{article-id}.json" \
  | jq '{id: .article.id, body_html: .article.body_html}'
```

By the way, we're about to start editing articles instead of just reading them, so this is a good time to think about backing up data. Shopify does not offer a bulk data export function, but we can back up all of our articles in nice JSON format by running just

```bash
curl \
  -X GET \
  "https://{api-key}:{password}@{domain}/admin/blogs/{blog-id}/articles/{article-id}.json"
```

on every article ID. Wrap that in a ``for`` loop in a shell script and save your articles somewhere, just in case something goes horribly wrong.

Now we can get the contents of an arbitrary post in JSON format; we just need to add a ``rel="nofollow"`` attribute to each ``<a>`` tag. Take note that double quotes in JSON have to be escaped. We can make this change by piping into ``sed``:

```bash
sed 's/<a \([^>]*\)>/<a \1 rel=\\"nofollow\\">/g'
```

This command looks for ``<a ...>`` in the input stream and replaces it with ``<a ... rel=\"nofollow\">``; the output is still valid JSON.

Say we've edited our post JSON now and want to reupload it. We can do this with ``curl`` as well. If your edited JSON is in ``article.json``, say

```bash
curl \
  -H "Accept: application/json" \
  -H "Content-Type: application/json" \
  -X PUT \
  -d @article.json \
  "https://{api-key}:{password}@{domain}/admin/blogs/{blog-id}/articles/{article-id}.json"
```

The response will be the edited post. You can check that the edit worked by looking at the post source in the Shopify web interface.

We can put these commands together in a shell script that takes the article ID as an argument, so that editing a single post is easy. But we've got a ton of posts to edit, so we'd rather not run even the script by hand on each one. So we can even wrap this call in a script that takes our list of all article IDs and edits each one. I'll leave all that as an exercise.


## Checking the Results

So far we've been able to add ``rel="nofollow"`` to every anchor in every blog post. But there may be external links elsewhere on the site that didn't get changed. We can find those using ``wget``:

```bash
wget \
  --recursive \
  --level=100 \
  --domains {domain} \
  --html-extension \
  --no-parent \
  --page-requisites \
  --output-file=log.txt \
  https://{domain}
```

This command downloads everything under your domain and puts it in the directory ``{domain}``. On your site you may need to play with the ``--level`` parameter to make sure you get everything, especially if your site is not very well connected.

Now we can look for links to external domains like this:

```bash
# Build list of page filenames
find {domain}/ -name '*.html' \
  > all-pages.txt


# Record bad anchors on each page
for f in $( cat all-pages.txt ); do
  BADS=$( cat $f | hxclean | hxnormalize -x | hxselect -s '\n' 'a' \
    | grep -v '^ ' \
    | grep -v 'href="/' \
    | grep -v 'href="#' \
    | grep -v 'name=' \
    | grep -v 'href="http://{domain}' \
    | grep -v 'href="https://{domain}' \
    | grep -v 'href="{' \
    | grep -v 'rel="nofollow"' \
  )
  if [ -n "$BADS" ]; then
    echo $f >> links.txt
    echo "$BADS" >> links.txt
    echo >> links.txt
  fi
done
```

Watch out for ``hxclean``, ``hxnormalize``, and ``hxselect``: these are part of the ``html-xml-utils`` suite and may not be installed. But they are super useful! ``hxselect``, for instance, is like ``grep`` with CSS selectors.

These commands (1) build a list of all the HTML files on your site, then for each one (2) extract the ``<a>`` tags, one per line, and (3) filter out any relative links, named anchors, internal links, and links with a ``rel="nofollow"`` attribute. It gathers the results in a file called ``links.txt`` which lists any "bad" links with the URL of the page they were found on. This will catch links on product pages, about pages, and so on. You can add extra filters here if there are any external links you don't care about, like social media links. You can then fix these bad links by hand if there aren't too many, or with a script like we did with blog posts.


## The End

The API is a really powerful way to interact with our Shopify shop. This is how Shopify apps work, by the way. With the right scripts we can do lots of bulk editing and maintenance tasks that are difficult or impossible to do by hand.
