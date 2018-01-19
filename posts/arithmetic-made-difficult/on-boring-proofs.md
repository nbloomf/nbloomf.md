---
title: On Boring and Repetitive Proofs
author: nbloomf
date: 2017-06-01
tags: arithmetic-made-difficult
slug: boring-proofs
---

So far in this series we've defined two basic "data types", the natural numbers and lists. Both types nailed down some kind of recursive structure and each came with an induction principle, which we used to establish a kind of computational algebra. On $\nats$ the computational algebra was just arithmetic, while on lists it was... different, but still turns out to be useful. But in both cases recursion and induction make it possible to

1. Compute stuff, and
2. Prove things about the stuff we compute.

Something else we might notice about these proofs is that they are *super boring and repetitive*. The induction proofs are essentially all the same, and the definitions are set up so that really no nonobvious leaps of logic are needed. From a mathematician's perspective, this is awful! I shouldn't presume to speak to the aesthetic judgments of other people, but I will anyway. My guess is that most people would say that as a whole, the proofs in this series of posts so far lack that special something called *elegance*. An elegant proof is one that's particularly short, or has a high ratio of power to effort, or draws together otherwise far-flung ideas. To my eye none of that is happening here.

On the other hand, I find it comforting that such pedestrian techniques can go so far. Because elegant proofs also require us to be *really clever* before we can find them! And I for one am not really that clever even on my best days. But this combination of **initial algebra** and **induction principle** is a set of dependable tools. Once we're comfortable with them, using them to make provably correct programs is a matter of putting in the effort.


What's Next
-----------

We've seen several different functions on $\bool$, $\nats$, and $\lists{A}$ so far which have some properties in common. For example, $\band : \bool \times \bool \rightarrow \bool$ satisfies $$\band(\band(a,b),c) = \band(a,\band(b,c)).$$ But also $\nplus : \nats \times \nats \rightarrow \nats$ satisfies $$\nplus(\nplus(a,b),c) = \nplus(a,\nplus(b,c)),$$ and $\cat : \lists{A} \times \lists{A} \rightarrow \lists{A}$ satisfies $$\cat(\cat(a,b),c) = \cat(a,\cat(b,c)).$$

In mathematics, when two or more different "objects" which are known to be interesting share some common *behavior*, experience has shown that it is useful to abstract out the essence of commonality. In the above examples the common behavior is that we have a function $f : A \times A \rightarrow A$ which satisfies $$f(f(a,b),c) = f(a,f(b,c)).$$ Of course functions with this property are called *associative*. Any theorem we can prove about an abstract $f$ using only the assumption that $f$ is associative immediately applies to *all* associative functions.

In the next few posts we will draw out, from our examples so far, some abstractions which are known to be particularly useful.
