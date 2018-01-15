MKSHELL=/bin/bash

targets:VQ:
  echo 'targets'                                      | doppler lightgreen
  echo '  all       : everything'                     | doppler lightcyan
  echo '  watch     : serve pages at localhost:31337' | doppler lightcyan
  echo '  build     : generate nbloomf.github.io'     | doppler lightcyan
  echo '  site      : compile site executable'        | doppler lightcyan
  echo '  favicons  : generate favicons'              | doppler lightcyan
  echo '  winfiles  : convert raw file line endings'  | doppler lightcyan
  echo '  blankpost : echo empty post template'       | doppler lightcyan

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

test-info:VQ:
  echo 'amd' | doppler lightgreen
  AMD="$(stack test amd 2> /dev/null)"
  AMDTESTS="$(echo "${AMD}" | grep '^+++' | wc -l)"
  echo '  tests: ' ${AMDTESTS} | doppler lightblue
  AMDCASES="$(echo "${AMD}" | grep '^+++' | awk '{t+=$4}; END {print t}')"
  echo '  cases: ' ${AMDCASES} | doppler lightblue




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



#=========#
# writing #
#=========#

blankpost:VQ:
  echo '---'
  echo 'title: '
  echo 'author: nbloomf'
  echo 'date:' `date +%F`
  echo 'tags: '
  echo '---'
  echo

sniff-amd:VQ: \
  sniff-amd-fencediv \
  sniff-amd-plaindiv \
  sniff-amd-nestdiv

#-- use consistent syntax for fenced divs --#
sniff-amd-fencediv:VQ:
  FENCEDIV=$( grep '^:::' posts/arithmetic-made-difficult/* \
    | grep -v ':::::: axiom :::::::' \
    | grep -v ':::::: definition ::' \
    | grep -v ':::::: theorem :::::' \
    | grep -v ':::::: corollary :::' \
    | grep -v '::: proof ::::::::::' \
    | grep -v '::: test :::::::::::' \
    | grep -v '::::::::::::::::::::' )
  if [ -z "$FENCEDIV" ]; then
    echo 'Fenced Divs OK' | doppler lightgreen
  else
    echo 'Fenced Divs' | doppler lightred
    echo $(echo "$FENCEDIV" | wc -l) 'problems found' | doppler lightred
    echo "$FENCEDIV"
  fi

#-- do not use literal divs --#
sniff-amd-plaindiv:VQ:
  PLAINDIV=$( grep -e '<div[> ]' -e '</div>' posts/arithmetic-made-difficult/* || true )
  if [ -z "$PLAINDIV" ]; then
    echo 'Plain Divs OK' | doppler lightgreen
  else
    echo 'Plain Divs' | doppler lightred
    echo $(echo "$PLAINDIV" | wc -l) 'problems found' | doppler lightred
    echo "$PLAINDIV"
  fi

#-- use consistent structure for divs --#
sniff-amd-nestdiv:VQ:
  NESTDIV=$( grep '^:::' posts/arithmetic-made-difficult/* \
    | sed 's/posts\/arithmetic-made-difficult\///' \
    | sed 's/:::::: axiom :::::::$/axm/' \
    | sed 's/:::::: definition ::$/def/' \
    | sed 's/:::::: theorem :::::$/thm/' \
    | sed 's/:::::: corollary :::$/cor/' \
    | sed 's/::: proof ::::::::::$/prf/' \
    | sed 's/::: test :::::::::::$/tst/' \
    | sed 's/::::::::::::::::::::$/cls/' \
    | sed '$!N;/^\([^:]*:\)\(.*\)\(\n\)\1/!P;s//\3\1\2 /;D' \
    | sed 's/def cls//g' \
    | sed 's/axm cls//g' \
    | sed 's/cor cls//g' \
    | sed 's/thm prf cls tst cls cls//g' \
    | sed 's/thm prf cls cls//g' \
    | sed 's/cor tst cls cls//g' \
    | sed 's/ *$//' \
    | sed '/:$/d' )
  if [ -z "$NESTDIV" ]; then
    echo 'Nested Divs OK' | doppler lightgreen
  else
    echo 'Nested Divs' | doppler lightred
    echo $( echo "$NESTDIV" | wc -l ) 'problems found' | doppler lightred
    echo "$NESTDIV"
  fi
