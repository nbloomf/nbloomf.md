---
title: Printable Graph Paper
author: nbloomf
date: 2015-10-10
tags: latex
---

Made with LaTeX and TikZ.

## Rectangular

[PDF](/pdf/graph-paper/rect.pdf) and [tex source](/pdf/graph-paper/rect.tex).

```latex
\begin{tikzpicture}[scale=0.47]
  \pgfmathsetmacro{\h}{55}
  \pgfmathsetmacro{\w}{40}
  \pgfmathsetmacro{\sub}{1 / 5}
  \pgfmathsetmacro{\sup}{5}

  % Subdivisions
  \foreach \x in {0,\sub,...,\w} {%
    \draw [line width=0.3, color=lightgray, opacity=0.4] (\x,0) -- (\x,\h);%
  }%
  \foreach \y in {0,\sub,...,\h} {%
    \draw [line width=0.3, color=lightgray, opacity=0.4] (0,\y) -- (\w,\y);%
  }%

  % Divisions
  \foreach \x in {0,...,\w} {%
    \draw [line width=0.6, color=lightgray, opacity=0.6] (\x,0) -- (\x,\h);%
  }%
  \foreach \y in {0,...,\h} {%
    \draw [line width=0.6, color=lightgray, opacity=0.6] (0,\y) -- (\w,\y);%
  }%

  % Superdivisions
  \foreach \x in {0,\sup,...,\w} {%
    \draw [line width=0.9, color=lightgray, opacity=0.8] (\x,0) -- (\x,\h);%
  }%
  \foreach \y in {0,\sup,...,\h} {%
    \draw [line width=0.9, color=lightgray, opacity=0.8] (0,\y) -- (\w,\y);%
  }%
\end{tikzpicture}
```


## Hexagonal because why not

[PDF](/pdf/graph-paper/hex.pdf) and [tex source](/pdf/graph-paper/hex.tex).

```latex
\begin{tikzpicture}[scale=0.499, yscale=1, xscale=1, rotate=0]
  \pgfmathsetmacro{\h}{31-1}
  \pgfmathsetmacro{\w}{14-1}

  \clip (0,0) rectangle (3*\w, {sqrt(3)*\h});

  \foreach \x in {0,...,\h} {%
    \foreach \y in {0,...,\w} {%
      \draw [line width=0.6, color=lightgray]%
        (3*\y,{sqrt(3)*\x})++(0:1) -- ++(120:1)%
          -- ++(180:1) -- ++(240:1) -- ++(300:1)%
          -- ++(360:1) -- ++(60:1);%
      \draw [line width=0.6, color=lightgray]%
        (1.5+3*\y,{sqrt(3)*(0.5+\x)})++(0:1)%
          -- ++(120:1) -- ++(180:1) -- ++(240:1)%
          -- ++(300:1) -- ++(360:1) -- ++(60:1);%
    }%
  }%

  \draw [color=gray, line width=0.6] (0,0) rectangle (3*\w, {sqrt(3)*\h});
\end{tikzpicture}
```
