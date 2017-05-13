---
title: LaTeX Examples
author: nbloomf
date: 2017-05-14
tags: latex
---

This post contains some links and examples I threw together to help students getting started with LaTeX.

LaTeX is a markup language for academic and technical writing. It is the defacto standard way to produce publication-ready documents in mathematics, including books and journal articles. The goal of this tutorial is to help you learn to use LaTeX to produce documents.


Why should I learn LaTeX?
-------------------------

The only real answer to this question is "because you want to". You can certainly have a happy life without knowing anything at all about LaTeX, and it does have a steep learning curve.

BUT.

If you find yourself frequently writing complex equations, or writing documents with complicated cross-referencing or bibliographies, or wanting to publish a technical book or paper, or wanting to communicate math over the web, then LaTeX can make your life better in several concrete ways.


What is LaTeX?
--------------

* **It is a markup language for technical writing.**
* **It is not a single monolithic program.** It is an ecosystem of tools that work together.
* **It gives the author control.** There are IDEs which behave like word processors, hiding away some of the details. Experienced users can also dig into the guts for more power.
* **It does not have a single designer.** Many people have worked together over many years to build and maintain the LaTeX ecosystem we have today.
* **It is not a commercial product.** You do not have to buy a license or get permission to use it.
* **It is industrial strength.** TeX, the software at the heart of the ecosystem, was explicitly designed for producing "camera-ready" books, and there are commercial publishing houses which use it.
* **It is designed for technical and academic text.** Complex equations and diagrams, cross references, bibliographies, numbering


Installing LaTeX
----------------

On Windows:

* [Download and install MikTeX](http://www.miktex.org/download)
* [Download and install TeXMaker](http://www.xm1math.net/texmaker/download.html)


Resources
---------

* [LaTeX Wikibook](https://en.wikibooks.org/wiki/LaTeX): Really great place to find quick answers.
* [TeX StackExchange](http://tex.stackexchange.com/): I wouldn't start searching here, but if you Google search for ``latex blah`` where ``blah`` is some problem you have, typically links here have good info.


Examples
--------

This is a list of example LaTeX documents which demonstrate how to do some specific things.

* **A (nearly) minimal latex document** ([tex windows](/raw/tex/win/examples/hello.tex)) ([tex unix](/raw/tex/unix/examples/hello.tex)) ([pdf](/pdf/tex-examples/hello.pdf))

    Not *the* simplest possible tex document, but pretty close.

* **Styling text** ([tex windows](/raw/tex/win/examples/text.tex)) ([tex unix](/raw/tex/unix/examples/text.tex)) ([pdf](/pdf/tex-examples/text.pdf))

    Bold, italics, underlined text, quotation marks, as well as diacritics.

* **The parts of a tex file** ([tex windows](/raw/tex/win/examples/format.tex)) ([tex unix](/raw/tex/unix/examples/format.tex)) ([pdf](/pdf/tex-examples/format.pdf))

    A bit about what "documentclass" and "begin document" mean.

* **Writing mathematics** ([tex windows](/raw/tex/win/examples/math.tex)) ([tex unix](/raw/tex/unix/examples/math.tex)) ([pdf](/pdf/tex-examples/math.pdf))

    Typing equations.

* **Lists** ([tex windows](/raw/tex/win/examples/lists.tex)) ([tex unix](/raw/tex/unix/examples/lists.tex)) ([pdf](/pdf/tex-examples/lists.pdf))

    For when you have a bunch of things and want to write them.

* **Graphics** ([tex windows](/raw/tex/win/examples/graphics.tex)) ([tex unix](/raw/tex/unix/examples/graphics.tex)) ([pdf](/pdf/tex-examples/graphics.pdf)) ([image](/raw/gfx/tex-examples/dice.png))

    Including pictures in your documents. To compile this example, you will need to put the image file ``dice.png`` inside a folder called ``gfx`` next to your tex file.

* **Packages** ([tex windows](/raw/tex/win/examples/packages.tex)) ([tex unix](/raw/tex/unix/examples/packages.tex)) ([pdf](/pdf/tex-examples/packages.pdf))

    Going beyond plain LaTeX.

* **Document Structure** ([tex windows](/raw/tex/win/examples/structure.tex)) ([tex unix](/raw/tex/unix/examples/structure.tex)) ([pdf](/pdf/tex-examples/structure.pdf))

    Breaking up a large document into subparts.

* **Files** ([tex windows](/raw/tex/win/examples/files.tex)) ([tex unix](/raw/tex/unix/examples/files.tex)) ([pdf](/pdf/tex-examples/files.pdf))

    The files that make up a LaTeX project.

* **Counters, Labels, and Cross References** ([tex windows](/raw/tex/win/examples/counters.tex)) ([tex unix](/raw/tex/unix/examples/counters.tex)) ([pdf](/pdf/tex-examples/counters.pdf))

    Linking from one part of a document to another.

* **Bibliographies** ([tex windows](/raw/tex/win/examples/citations.tex)) ([tex unix](/raw/tex/unix/examples/citations.tex)) ([pdf](/pdf/tex-examples/citations.pdf)) ([bib windows](/raw/tex/win/examples/citations.bib)) ([bib unix](/raw/tex/unix/examples/citations.bib))

    Citing other works. For this example you will also need the ``bib`` file.

* **Slideshows** ([tex windows](/raw/tex/win/examples/slides.tex)) ([tex unix](/raw/tex/unix/examples/slides.tex)) ([pdf](/pdf/tex-examples/slides.pdf))

    Slick presentations with the ``beamer`` class.
