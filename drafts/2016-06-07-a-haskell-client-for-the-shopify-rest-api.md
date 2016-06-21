---
title: A Haskell client for the Shopify REST API
author: nbloomf
date: 2016-06-07
---

My wife Stacie is a designer and illustrator and sells art and other things on the Shopify platform (shameless plug: her online shop is called [Gingiber](http://gingiber.com)). Stacie is the brains and the talent behind Gingiber; I don't do much other than help move heavy things, courier things, and sometimes make changes to the online shop.

Shopify essentially abstracts away some of the hairier details of running an online shop: they handle payment processing and hosting, leaving everything else up to the shop owner. I'll call the abstract shop that Shopify provides a *shoppe*. From the shop owner's perspective, a shoppe is just a bunch of data. Some of that data represents the web pages of the shop, some represents the products for sale, and so on.

There are two basic ways shop owners can edit their shoppes. The simplest way is a web-based CMS-like interface much like Wordpress offers for editing blogs. This interface is simple to use, but suffers from the issues that plague any GUI. Everything must be done manually, and because interaction happens over the network, it is slow. The second editing method is what I'm interested in today. Shopify also provides a REST API which can be used to edit a shoppe programmatically.

REST is short for REpresentational State Transfer. The complete history and [details](http://en.wikipedia.org/wiki/Representational_state_transfer) of REST are beyond me, but the important thing is this: REST is a strategy for allowing two or more programs to communicate *statelessly*. That is, programs communicate by sending requests to each other and receiving responses, and they do not need to keep track of a context of previously handled requests. The HTTP protocol is well-suited to REST APIs; it is a standardized way to send requests over a network using one of several "verbs" including GET, PUT, and POST. API, by the way, is just the interface of a program -- how we can use it.

And so, Shopify provides a REST API. Each shoppe has
* A bunch of **data objects** of different types, like "product" and "article"; these objects are represented using JSON and can be thought of as records with named fields.
* A bunch of **value types**; restrictions on the values of some fields. JSON naturally only allows the representation of Javascript numbers (which are a hot mess, holy hell) and strings. But some fields can really only take on a limited range of values, like "country name".
* A bunch of **endpoints**; these are the specific URLs which, when sent an appropriate request, respond with a JSON object.
* For each endpoint, zero or more **endpoint options** which alter the endpoint's response.

To keep anyone from being able to mess with anyone else's shoppe, to use the API we also have to provide an API key and password: these are credentials, issued by a shoppe, which allow client programs to interact with it. Putting this together we can send an HTTP request to a URL like

    verb https://api-key:password@shop-name.shopify.com/endpoint.json?options

and if all goes well the server will respond with a JSON-encoded object. This is just an HTTP request, so we can try it out on the command line with ``curl`` or even using a web browser. By chaining together several requests we can do complicated things. Of course sending all these HTTP requests by hand with ``curl``, while possible, is slow and error-prone -- not much of an improvement over the web-based GUI. So instead we'd rather be able to write programs in a more structured language which interfaces with the REST API behind the scenes. That "behind the scenes" part means we want a *client library* for communicating with the Shopify API. By the way- this is why REST APIs over HTTP are so successful: we can write the client in *any language we want to*. And in fact client libraries already exist for the most popular languages: Ruby, Javascript, and others.

With each project I work on, I try to only learn one or two new things at once. I find that my time is more productively spent this way. Since I am new to HTTP and REST, I'll stick with the language I'm most comfortable with: Haskell. Unfortunately I can't find a mature Haskell client library for Shopify's REST API, so I'll be writing my own.

## Modeling the API

To write a client library, we need to model the basic parts of the API inside Haskell. The various kinds of data objects are naturally types, as are the value types. Endpoints can be thought of as functions, and endpoint options are function arguments. Here's an example to a first approximation: the API has an endpoint called ``GET /admin/metafields.json`` which, given some optional options, returns some JSON representing a "Metafields" object. We might hope to represent this in Haskell as a function like so:

    getMetafields :: Credentials -> Options -> Metafields
    getMetafields = ...

This doesn't quite work- although the API is stateless, it is not referentially transparent: two requests to the same endpoint using the same options but sent at different times may return different responses, and some requests explicitly change the state of our shoppe. So the *order* of our requests matters. The usual way to model order-dependent computations with Haskell is using a **monad**. Let's call this the ``Haskify`` monad. By the way, now that we're using a monad, we can stuff the ``Credentials`` into an implicit state value to get passed around. So an updated version of getMetafields might look like

    getMetafields :: Options -> Haskify Metafields
    getMetafields = ...
