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
  echo '  sniff-amd : style sniffs'                   | doppler lightcyan
  echo '  test-info : test stats'                     | doppler lightcyan

all:VQ: build watch install test



#========#
# basics #
#========#

install:VQ:
  stack install

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



#======#
# test #
#======#

test:VQ:
  shelltest test/ --color --threads=16 --execdir
  stack test

test-info:VQ:
  echo 'amd' | doppler lightgreen
  STMTS=$( grep '^>   testName "' posts/arithmetic-made-difficult/* | wc -l )
  echo '  statements: ' ${STMTS} | doppler lightblue
  AMD="$(stack test amd 2> /dev/null)"
  AMDTESTS="$(echo "${AMD}" | grep '^+++' | wc -l)"
  echo '  tests:      ' ${AMDTESTS} | doppler lightblue
  AMDCASES="$(echo "${AMD}" | grep '^+++' | awk '{t+=$4}; END {print t}')"
  echo '  cases:      ' ${AMDCASES} | doppler lightblue

check-info:VQ:
  echo 'amd' | doppler lightgreen
  CHECKS=$( grep '^ &     \\' posts/arithmetic-made-difficult/* | wc -l )
  echo '  checked equalities: ' ${CHECKS} | doppler lightblue



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



#========#
# sniffs #
#========#

sniff-amd:VQ: \
  sniff-amd-fencediv \
  sniff-amd-plaindiv \
  sniff-amd-nestdiv \
  sniff-amd-balance \
  sniff-amd-refname \
  sniff-amd-eqnarray \
  sniff-amd-slugs \
  sniff-amd-testtext \
  sniff-amd-rewrite

#-- use consistent syntax for fenced divs --#
sniff-amd-fencediv:VQ:
  FENCEDIV=$( grep '^:::' posts/arithmetic-made-difficult/* \
    | grep -v ':::::: axiom :::::::' \
    | grep -v ':::::: definition ::' \
    | grep -v ':::::: theorem :::::' \
    | grep -v ':::::: corollary :::' \
    | grep -v '::: proof ::::::::::' \
    | grep -v '::: test :::::::::::' \
    | grep -v '::::::::::::::::::::' \
    || true )
  if [ -z "$FENCEDIV" ]; then
    echo 'Fenced Divs OK' | doppler lightgreen
  else
    echo 'Fenced Divs' | doppler lightred
    echo $(echo "$FENCEDIV" | wc -l) 'problems found' | doppler lightred
    echo "$FENCEDIV"
  fi

#-- do not use literal divs --#
sniff-amd-plaindiv:VQ:
  PLAINDIV=$( grep -e '<div[> ]' -e '</div>' posts/arithmetic-made-difficult/* \
    || true )
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
    | sed '/:$/d' \
    || true )
  if [ -z "$NESTDIV" ]; then
    echo 'Nested Divs OK' | doppler lightgreen
  else
    echo 'Nested Divs' | doppler lightred
    echo $( echo "$NESTDIV" | wc -l ) 'problems found' | doppler lightred
    echo "$NESTDIV"
  fi

#-- balanced delimiters --#
sniff-amd-balance:VQ:
  BALANCE=$( balance -d '\left\{ \right. ( ) { }' posts/arithmetic-made-difficult/* )
  if [ -z "$BALANCE" ]; then
    echo 'Delimiters OK' | doppler lightgreen
  else
    echo 'Delimiters' | doppler lightred
    echo $( echo "$BALANCE" | wc -l ) 'problems found' | doppler lightred
    echo "$BALANCE"
  fi
  
  BALANCE=$( grep -n '^ & ' posts/arithmetic-made-difficult/* | balance -l || true )
  if [ -z "$BALANCE" ]; then
    echo "Eqnarray Delimiters OK" | doppler lightgreen
  else
    echo "Eqnarray Delimiters" | doppler lightred
    echo $( echo "$BALANCE" | wc -l ) 'problems found' | doppler lightred
    echo "$BALANCE"
  fi

#-- consistent reference names --#
sniff-amd-refname:VQ:
  REFNAME=$( grep '^\[\](#' posts/arithmetic-made-difficult/* \
    | sed 's/\[\](\(#[^)]*\)).*/ \1/' \
    | grep -v '#def-[a-z-]*$' \
    | grep -v '#thm-[a-z-]*' \
    || true )
  if [ -z "$REFNAME" ]; then
    echo 'Reference Names OK' | doppler lightgreen
  else
    echo 'Reference Names' | doppler lightred
    echo $( echo "$REFNAME" | wc -l ) 'problems found' | doppler lightred
    echo "$REFNAME"
  fi

#-- eqnarray command on separate line --#
sniff-amd-eqnarray:VQ:
  EQNARRAY=$( grep \
      -e '.$$\\begin{eqnarray\*}' \
      -e '$$\\begin{eqnarray\*}.' \
      -e '.\\end{eqnarray\*}$\$' \
      -e '\\end{eqnarray\*}$$.' \
      posts/arithmetic-made-difficult/* \
    || true )
  if [ -z "$EQNARRAY" ]; then
    echo 'Eqnarray OK' | doppler lightgreen
  else
    echo 'Eqnarray' | doppler lightred
    echo $( echo "$EQNARRAY" | wc -l ) 'problems found' | doppler lightred
    echo "$EQNARRAY"
  fi

#-- slugs exist, have consistent form, and are unique --#
sniff-amd-slugs:VQ:
  SLUGS=$( grep '^slug: ' posts/arithmetic-made-difficult/* \
    | grep -v 'slug: [a-z-]*$' \
    || true )
  if [ -z "$SLUGS" ]; then
    echo 'Slug form OK' | doppler lightgreen
  else
    echo 'Slug form' | doppler lightred
    echo $( echo "$SLUGS" | wc -l ) 'problems found' | doppler lightred
    echo "$SLUGS"
  fi
  
  SLUGS=$( grep '^slug: ' posts/arithmetic-made-difficult/* \
    | cut -d ' ' -f 2 \
    | sort \
    | uniq -c \
    | grep -v ' *1' \
    || true )
  if [ -z "$SLUGS" ]; then
    echo 'Slug uniqueness OK' | doppler lightgreen
  else
    echo 'Slug uniqueness' | doppler lightred
    echo $( echo "$SLUGS" | wc -l ) 'problems found' | doppler lightred
    echo "$SLUGS"
  fi
  
  SLUGS=$( grep -L '^slug: ' \
    posts/arithmetic-made-difficult/*.lhs \
    posts/arithmetic-made-difficult/*.md \
    || true )
  if [ -z "$SLUGS" ]; then
    echo 'Slug existence OK' | doppler lightgreen
  else
    echo 'Slug existence' | doppler lightred
    echo $( echo "$SLUGS" | wc -l ) 'problems found' | doppler lightred
    echo "$SLUGS"
  fi

#-- test descriptions are unique --#
sniff-amd-testtext:VQ:
  TESTTEXT=$( grep '^>   testName ' posts/arithmetic-made-difficult/* \
    | sed 's/" \$$//' \
    | sed 's/>   testName "/ @ /' \
    | awk -F '@' 'num[$2]++{if (num[$2]==2) print prev[$2]; print} {prev[$2]=$0}' \
    || true )
  if [ -z "$TESTTEXT" ]; then
    echo 'Test text OK' | doppler lightgreen
  else
    echo 'Test text' | doppler lightred
    echo $( echo "$TESTTEXT" | wc -l ) 'problems found' | doppler lightred
    echo "$TESTTEXT"
  fi

#-- check term rewrites --#
sniff-amd-rewrite:VQ:
  REWRITE=$( grep -n -C 1 '^ &     \\' posts/arithmetic-made-difficult/* \
    | sed '/^--$/d' \
    | sed 's/^[a-zA-Z\/.-]*[0-9][0-9]*-//' \
    | sed 's/^ &   & //' \
    | sed 's/^ & = & //' \
    | sed 's/^   = & //' \
    | sed 's/ \\\\$//' \
    | tr '&' '\n' \
    | sed 's/     \\href{\([^}]*\)}/===\1===/' \
    | sed 's/     \\hyp{\([^}]*\)}/\1/' \
    | sed 's/     \\let{\([^}]*\)}/\1/' \
    | sed 's/[ ]*$//' \
    | paste - - - - \
    | awk -F"\t" '{print $2 "\t" $3 "\t" $1 "\t" $4}' \
    | sed -f amd-rules.txt \
    | rewrite-term \
    || true )
  if [ -z "$REWRITE" ]; then
    echo 'Term rewrites OK' | doppler lightgreen
  else
    echo 'Term rewrites' | doppler lightred
    echo $( echo "$REWRITE" | wc -l ) 'problems found' | doppler lightred
    echo "$REWRITE"
  fi

#-- check existence of crossrefs --#
sniff-amd-crossref:VQ:
  CROSS=$( grep '^ & = & ' posts/arithmetic-made-difficult/* || true )
  if [ -z "$CROSS" ]; then
    echo 'Cross references OK' | doppler lightgreen
  else
    echo 'Cross references' | doppler lightred
    echo "$CROSS"
    echo #( echo "$CROSS" | wc -l ) 'problems found' | doppler lightred
  fi
