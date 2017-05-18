MKSHELL=/bin/bash

PATH = `{pwd}/_bin/sth:`{pwd}/_bin/amd:$PATH

targets:VQ:
  echo 'compile'                                    | doppler lightgreen
  echo '  all      : everything'                    | doppler lightcyan
  echo '  watch    : serve pages at localhost:8000' | doppler lightcyan
  echo '  build    : generate nbloomf.github.io'    | doppler lightcyan
  echo '  site     : compile site'                  | doppler lightcyan
  echo '  literate : compile literate posts'        | doppler lightcyan
  echo '  favicons : generate favicons'             | doppler lightcyan
  echo '  winfiles : convert raw file line endings' | doppler lightcyan
  echo 'test'                                       | doppler lightgreen
  echo '  amd-test : run amd tests'                 | doppler lightcyan
  echo '  sth-test : run sth tests'                 | doppler lightcyan

all:VQ: literate build watch



#========#
# basics #
#========#

watch:VQ: site
	echo 'view at localhost:8000' | doppler lightcyan
	./site watch

build:VQ: site favicons winfiles
	./site clean
	./site build
	cp -r _site/. ../nbloomf.github.io/
	echo "nbloomf.github.io up to date" | doppler lightgreen

site:Q: site.lhs
  echo 'Compiling site...' | doppler lightgreen
  ghc --make -threaded site.lhs
  rm site.o site.hi

check:VQ:
	wget -r -nv --spider https://nbloomf.github.io
	rm -r nbloomf.github.io



#===================#
# generate favicons #
#===================#

favicons:VQ:                   \
  raw/gfx/icon/favicon-32.png  \
  raw/gfx/icon/favicon-57.png  \
  raw/gfx/icon/favicon-114.png \
  raw/gfx/icon/favicon-152.png
	echo "favicons up to date" | doppler lightgreen

raw/gfx/icon/favicon-32.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-32" | doppler lightblue
  inkscape -z -e $target -w 32 -h 32 $prereq

raw/gfx/icon/favicon-57.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-57" | doppler lightblue
  inkscape -z -e $target -w 57 -h 57 $prereq

raw/gfx/icon/favicon-114.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-114" | doppler lightblue
  inkscape -z -e $target -w 114 -h 114 $prereq

raw/gfx/icon/favicon-152.png:Q: raw/gfx/icon/info.svg
  echo "generating favicon-152" | doppler lightblue
  inkscape -z -e $target -w 152 -h 152 $prereq



#======================#
# convert line endings #
#======================#

winfiles:Q: `{find raw/tex/win/ -type f}
  echo "converted raw text to win line endings" | doppler lightgreen

raw/tex/win/%:Q: raw/tex/unix/%
  echo "converting $prereq" | doppler lightblue
  cat $prereq | awk '{ sub("$$", "\r"); print }' > $target



#========================#
# compile literate posts #
#========================#

literate:V: sth amd

literate-test:V: sth-test amd-test


#---------------------------#
# software tools in haskell #
#---------------------------#

STH_TOOLS = archive bubble charcombine charfullwidth charreplace compare compress concat copy count crypt detab echo entab escape examine expand getlines glyphcount import linenumber noop overstrike paginate pslineprint sentcount tail translit unescape wordcount wye

sth:VQ: sth-test

sth-test:VQ: sth-exe
  echo "testing sth..." | doppler lightblue
  (shelltest --color --execdir test/sth -- --threads=16)

sth-exe:VQ: ${STH_TOOLS:%=_bin/sth/sth-%}

_bin/sth/(.+):QR: posts/software-tools-in-haskell/dist/build/\1/\1
  echo "copying $stem1" | doppler lightcyan
  cp posts/software-tools-in-haskell/dist/build/$stem1/$stem1 $target

posts/software-tools-in-haskell/dist/%:VQ: sth-build

sth-build:VQ:
  echo "building sth..." | doppler lightblue
  (cd posts/software-tools-in-haskell; cabal install)


#---------------------------#
# arithmetic made difficult #
#---------------------------#

AMD_TOOLS = all-any at boolean cat coprime div divalg elt filter gcd lcm lcp length leq map max-min minus nat plus power prefix prime range rev tails-inits times tuple unzip zip

amd:VQ: amd-test

amd-test:VQ: amd-exe
  echo "testing amd..." | doppler lightblue
  (shelltest --color --execdir test/amd -- --threads=16)

amd-exe:VQ: ${AMD_TOOLS:%=_bin/amd/amd-%}

_bin/amd/(.+):QR: posts/arithmetic-made-difficult/dist/build/\1/\1
  echo "copying $stem1" | doppler lightcyan
  cp posts/arithmetic-made-difficult/dist/build/$stem1/$stem1 $target

posts/arithmetic-made-difficult/dist/%:VQ: amd-build

amd-build:VQ:
  echo "building amd..." | doppler lightblue
  (cd posts/arithmetic-made-difficult; cabal install)
