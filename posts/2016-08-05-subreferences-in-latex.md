---
title: Subreferences in LaTeX
author: nbloomf
date: 2016-08-05
categories: latex
tags: latex
---

This post is a note to myself about cross references in LaTeX. So if that's your thing, read on. :)

LaTeX makes cross references in large documents super easy. For instance, say we have a theorem we'd like to refer to later by number. This is done with ``\label{}`` and ``\ref{}``.

```latex
\begin{theorem}\label{thm}
Lorem ipsum dolor sit amet, consectetur
adipiscing elit.
\end{theorem}
    
Proof of Theorem \ref{thm} left to the reader.
```

There's a particular style of cross references for multi-part theorems that I particularly like. I'm sure it's very old, but I first saw it used in J. D. Monk's *Introduction to Set Theory*. In this style, theorems are numbered with Arabic numerals (1, 2, etc.) while their parts are numbered with small Roman numerals (i, ii, etc.). So in the text we might see something like this.

    Theorem 5. Lorem ipsum dolor sit amet,
    consectetur adipiscing elit.
       (i) Foo.
      (ii) Bar.
     (iii) Baz.

Then the text may later refer to this entire unit as "Theorem 5", or to a single part as "5(ii)". But if the proof of Theorem 5 is given in the text we don't need to qualify the parts of this theorem -- within the proof a reference like "(ii)" is unambiguous.

The problem is how to implement cross references like this with LaTeX simply and without polluting the label namespace too much. I'm sure anyone with more than a passing interest in LaTeX could figure it out, but here's my solution. It does require some label discipline and the ``enumitem`` package.

We can label the theorem with ``thm:lorem`` and then the parts with ``thm:lorem:foo``, ``thm:lorem:bar``, and ``thm:lorem:baz``. Now ``\ref{thm:lorem}`` refers to the theorem counter, while ``\ref{thm:lorem:bar}`` refers to the enumerate counter. We can refer to a specific part with ``\ref{thm:lorem}\ref{thm:lorem:bar}``. This is redundant, but if we're disciplined with qualifying labels we can use an additional command like

```latex
\newcommand{\sref}[2]{\ref{#1}\ref{#1:#2}}
```

and say ``\sref{thm:lorem}{bar}`` instead.

Here's a minimal working example.

* * *

```latex
\documentclass{article}

\usepackage{amsthm}
\usepackage{enumitem}

% Define theorem environment
\theoremstyle{definition}
\newtheorem{theorem}{Theorem}

% Style enumerate counter
\setlist[enumerate]{label=(\roman*)}

% Subreferences
\newcommand{\sref}[2]{\ref{#1}\ref{#1:#2}}



\begin{document}

\begin{theorem}\label{thm:lorem}
Lorem ipsum dolor sit amet, consectetur adipiscing elit.
\begin{enumerate}
  \item\label{thm:lorem:foo} Foo.
  \item\label{thm:lorem:bar} Bar.
  \item\label{thm:lorem:baz} Baz.
\end{enumerate}
\end{theorem}

We can refer to the entire Theorem \ref{thm:lorem},
to a single qualified part like \sref{thm:lorem}{bar},
or a single unqualified part like \ref{thm:lorem:baz}.

\end{document}
```
