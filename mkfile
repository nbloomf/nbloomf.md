MKSHELL=/bin/bash

targets:VQ:
  echo 'targets'                                     | doppler lightgreen
  echo '  all      : everything'                     | doppler lightcyan
  echo '  watch    : serve pages at localhost:31337' | doppler lightcyan
  echo '  build    : generate nbloomf.github.io'     | doppler lightcyan
  echo '  site     : compile site executable'        | doppler lightcyan
  echo '  favicons : generate favicons'              | doppler lightcyan
  echo '  winfiles : convert raw file line endings'  | doppler lightcyan

all:VQ: build watch install test



#========#
# basics #
#========#

watch:VQ: site
  export LANG=C
  echo 'view at localhost:31337' | doppler lightcyan
  site watch

build:VQ: site favicons winfiles
  site clean
  export LANG=C
  site build
  cp -r _site/. ../nbloomf.github.io/
  echo "nbloomf.github.io up to date" | doppler lightgreen

site:Q:
  echo 'Compiling site...' | doppler lightgreen
  stack install nbloomf-md

check:VQ:
  wget -r -nv --spider https://nbloomf.github.io
  rm -r nbloomf.github.io



install:VQ:
  stack install

test:VQ:
  shelltest test/ --color --threads=16 --execdir
  stack test



#===================#
# generate favicons #
#===================#

favicons:VQ:                     \
    raw/gfx/icon/favicon-32.png  \
    raw/gfx/icon/favicon-57.png  \
    raw/gfx/icon/favicon-114.png \
    raw/gfx/icon/favicon-152.png
  echo "favicons up to date" | doppler lightgreen

raw/gfx/icon/favicon-32.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-32" | doppler lightblue
  inkscape -z -e `pwd`/$target -w 32 -h 32 `pwd`/$prereq

raw/gfx/icon/favicon-57.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-57" | doppler lightblue
  inkscape -z -e `pwd`/$target -w 57 -h 57 `pwd`/$prereq

raw/gfx/icon/favicon-114.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-114" | doppler lightblue
  inkscape -z -e `pwd`/$target -w 114 -h 114 `pwd`/$prereq

raw/gfx/icon/favicon-152.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-152" | doppler lightblue
  inkscape -z -e `pwd`/$target -w 152 -h 152 `pwd`/$prereq



#======================#
# convert line endings #
#======================#

winfiles:Q: `{find raw/tex/win -type f}
  echo "converted raw text to win line endings" | doppler lightgreen

raw/tex/win/%:VQ: raw/tex/unix/%
  echo "converting $prereq" | doppler lightblue
  cat $prereq | awk '{sub("$","\r\n"); printf("%s",$0);}' > $target
