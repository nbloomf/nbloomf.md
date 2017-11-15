---
title: Machine Learning
---

I am trying to learn more about this hip "Machine Learning" thing the kids are all talking about. I'm the type that learns best about a thing by writing, so that's what this is.

The posts in this series are literate Haskell, and by the end comprise a crude library for constructing and (*slowly*) training basic neural networks. Everything is from scratch on Haskell 2010, and the only external dependency is QuickCheck (for tests). The point here is to understand the math, and no effort is put into speed.

Fair warning: this is pretty hideous. :)

1. [Prologue](/posts/ml/prologue.html)
2. Tensors
    * [Sizes and Indices](/posts/ml/Indices.html) and canonical [isomorphisms](/posts/ml/IndexIsos.html) among them.
    * [Tensors](/posts/ml/Tensors.html) and [tests](/posts/ml/Test/Tensors.html) of their properties.
    * [Tensor Functions](/posts/ml/TensorFunctions.html)
3. Optimization
    * [Gradients](/posts/ml/Gradients.html)
    * [Gradient Checking](/posts/ml/GradientChecking.html)
    * [Gradient Descent](/posts/ml/GradientDescent.html)
4. Supervised Learning
    * [Supervised Models](/posts/ml/SupervisedModels.html)
    * [Composite Models](/posts/ml/CompositeModels.html)
