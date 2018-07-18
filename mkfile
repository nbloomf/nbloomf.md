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
  echo '  add-hooks : link git hooks'                 | doppler lightcyan

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

add-hooks:VQ:
  rm .git/hooks/pre-commit
  ln hooks/pre-commit.sh .git/hooks/pre-commit



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
  sniff-amd-rewrite \
  sniff-amd-let \
  sniff-amd-latex \
  sniff-amd-import \
  sniff-amd-labels \
  sniff-amd-eqnarray-ends \
  sniff-amd-prelude \
  sniff-amd-arg-order

#-- use consistent syntax for fenced divs --#
sniff-amd-fencediv:VQ:
  echo 'Checking Fenced Divs' | doppler lightblue
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
    echo "$FENCEDIV"
    echo 'Fenced Divs' | doppler lightred
    echo $(echo "$FENCEDIV" | wc -l) 'problems found' | doppler lightred
    exit 1
  fi

#-- do not use literal divs --#
sniff-amd-plaindiv:VQ:
  echo 'Checking Plain Divs' | doppler lightblue
  PLAINDIV=$( grep -e '<div[> ]' -e '</div>' posts/arithmetic-made-difficult/* \
    || true )
  if [ -z "$PLAINDIV" ]; then
    echo 'Plain Divs OK' | doppler lightgreen
  else
    echo "$PLAINDIV"
    echo 'Plain Divs' | doppler lightred
    echo $(echo "$PLAINDIV" | wc -l) 'problems found' | doppler lightred
    exit 1
  fi

#-- use consistent structure for divs --#
sniff-amd-nestdiv:VQ:
  echo 'Checking Nested Divs' | doppler lightblue
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
    echo "$NESTDIV"
    echo 'Nested Divs' | doppler lightred
    echo $( echo "$NESTDIV" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- balanced delimiters --#
sniff-amd-balance:VQ:
  echo 'Checking Delimiters' | doppler lightblue
  BALANCE=$( balance -d '\left\{ \right. ( ) { }' posts/arithmetic-made-difficult/* )
  if [ -z "$BALANCE" ]; then
    echo 'Delimiters OK' | doppler lightgreen
  else
    echo "$BALANCE"
    echo 'Delimiters' | doppler lightred
    echo $( echo "$BALANCE" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi
  
  echo 'Checking Eqnarray Delimiters' | doppler lightblue
  BALANCE=$( grep -n '^ & ' posts/arithmetic-made-difficult/* | balance -l || true )
  if [ -z "$BALANCE" ]; then
    echo "Eqnarray Delimiters OK" | doppler lightgreen
  else
    echo "$BALANCE"
    echo "Eqnarray Delimiters" | doppler lightred
    echo $( echo "$BALANCE" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- consistent reference names --#
sniff-amd-refname:VQ:
  echo 'Checking Reference Names' | doppler lightblue
  REFNAME=$( grep '^\[\](#' posts/arithmetic-made-difficult/* \
    | sed 's/\[\]{\(#[^}]*\)}.*/ \1/' \
    | grep -v '#def-[a-z-]*$' \
    | grep -v '#thm-[a-z-]*' \
    || true )
  if [ -z "$REFNAME" ]; then
    echo 'Reference Names OK' | doppler lightgreen
  else
    echo "$REFNAME"
    echo 'Reference Names' | doppler lightred
    echo $( echo "$REFNAME" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- eqnarray command on separate line --#
sniff-amd-eqnarray:VQ:
  echo 'Checking Eqnarray' | doppler lightblue
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
    echo "$EQNARRAY"
    echo 'Eqnarray' | doppler lightred
    echo $( echo "$EQNARRAY" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- slugs exist, have consistent form, and are unique --#
sniff-amd-slugs:VQ:
  echo 'Checking Slug form' | doppler lightblue
  SLUGS=$( grep '^slug: ' posts/arithmetic-made-difficult/* \
    | grep -v 'slug: [a-z-]*$' \
    || true )
  if [ -z "$SLUGS" ]; then
    echo 'Slug form OK' | doppler lightgreen
  else
    echo "$SLUGS"
    echo 'Slug form' | doppler lightred
    echo $( echo "$SLUGS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi
  
  echo 'Checking Slug uniqueness' | doppler lightblue
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
    exit 1
  fi
  
  echo 'Checking Slug existence' | doppler lightblue
  SLUGS=$( grep -L '^slug: ' \
    posts/arithmetic-made-difficult/*.lhs \
    posts/arithmetic-made-difficult/*.md \
    || true )
  if [ -z "$SLUGS" ]; then
    echo 'Slug existence OK' | doppler lightgreen
  else
    echo "$SLUGS"
    echo 'Slug existence' | doppler lightred
    echo $( echo "$SLUGS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- test descriptions are unique --#
sniff-amd-testtext:VQ:
  echo 'Checking Test text' | doppler lightblue
  TESTTEXT=$( grep '^>   testName ' posts/arithmetic-made-difficult/* \
    | sed 's/" \$$//' \
    | sed 's/>   testName "/ @ /' \
    | awk -F '@' 'num[$2]++{if (num[$2]==2) print prev[$2]; print} {prev[$2]=$0}' \
    || true )
  if [ -z "$TESTTEXT" ]; then
    echo 'Test text OK' | doppler lightgreen
  else
    echo "$TESTTEXT"
    echo 'Test text' | doppler lightred
    echo $( echo "$TESTTEXT" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- no implicit prelude --#
sniff-amd-prelude:VQ:
  echo 'Checking No Implicit Prelude' | doppler lightblue
  PRELUDE=$( grep -B 1 '> module ' posts/arithmetic-made-difficult/* \
    | grep -v '^--$' \
    | paste - - \
    | grep -v '{-# LANGUAGE NoImplicitPrelude' \
    || true )
  if [ -z "$PRELUDE" ]; then
    echo 'No Implicit Prelude OK' | doppler lightgreen
  else
    echo "$PRELUDE"
    echo 'No Implicit Prelude' | doppler lightred
    echo $( echo "$PRELUDE" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- check term rewrites --#
sniff-amd-rewrite:VQ:
  echo 'Checking Term rewrites' | doppler lightblue
  cat sniff/amd/rules.txt \
    | grep -v '^#' \
    | awk -F"\t" '{print "s|===" $1 "===|" $2 "|";}' \
    > amd-rules-sed.txt
  REWRITE=$( grep -n -C 1 '^ &     \\h' posts/arithmetic-made-difficult/* \
    | sed '/^--$/d' \
    | sed 's/^[a-zA-Z\/.-]*[0-9][0-9]*-//' \
    | sed 's/^ &   & //' \
    | sed 's/^ & = & //' \
    | sed 's/^   = & //' \
    | sed 's/ \\\\$//' \
    | tr '&' '\n' \
    | sed 's/     \\href{\(.*\)}$/===\1===/' \
    | sed 's/     \\hyp{\(.*\)}$/\1/' \
    | sed 's/[ ]*$//' \
    | paste - - - - \
    | awk -F"\t" '{print $2 "\t" $3 "\t" $1 "\t" $4}' \
    | sed -f amd-rules-sed.txt \
    | rewrite-term --verify \
    || true )
  rm amd-rules-sed.txt
  if [ -z "$REWRITE" ]; then
    echo 'Term rewrites OK' | doppler lightgreen
  else
    echo "$REWRITE"
    echo 'Term rewrites' | doppler lightred
    echo $( echo "$REWRITE" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- check let rewrites --#
sniff-amd-let:VQ:
  echo 'Checking Let rewrites' | doppler lightblue
  cat sniff/amd/rules.txt \
    | grep -v '^#' \
    | awk -F"\t" '{print "s|===" $1 "===|" $2 "|";}' \
    > amd-rules-sed.txt
  REWRITE=$( grep -n -C 1 '^ &     \\let' posts/arithmetic-made-difficult/* \
    | sed '/^--$/d' \
    | sed 's/^[a-zA-Z\/.-]*[0-9][0-9]*-//' \
    | sed 's/^ &   & //' \
    | sed 's/^ & = & //' \
    | sed 's/^   = & //' \
    | sed 's/ \\\\$//' \
    | tr '&' '\n' \
    | sed 's/^     \\let{\(.*\)}$/\1/' \
    | sed 's/[ ]*$//' \
    | paste - - - - \
    | awk -F"\t" '{print $2 "\t" $3 "\t" $1 "\t" $4}' \
    | sed -f amd-rules-sed.txt \
    | rewrite-term --substitute \
    || true )
  rm amd-rules-sed.txt
  if [ -z "$REWRITE" ]; then
    echo 'Let rewrites OK' | doppler lightgreen
  else
    echo "$REWRITE"
    echo 'Let rewrites' | doppler lightred
    echo $( echo "$REWRITE" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- brute force search for valid crossrefs and edit script generator --#
sniff-amd-suggest:VQ:
  SUGGEST=$( awk '/^ & = & /{print FILENAME "\t" FNR "\t" prev "\t" $0} {prev=$0}' \
    posts/arithmetic-made-difficult/* \
    | sed 's/ & = & //g' \
    | sed 's/ &   & //g' \
    | sed 's/ \\\\//g' \
    | sed 's/,$//' \
    | sed 's/\.$//' \
    | grep -v 'circ' \
    | grep -v ' ' \
    | grep -v ':' \
    | grep -v '{(' \
    | rewrite-term --suggest sniff/amd/rules.txt \
    || true )
  echo "$SUGGEST"

#-- apply suggested crossref edits --#
sniff-amd-suggest-apply:VQ:
  chmod +x suggestions.txt
  ./suggestions.txt
  sed -i '' $'s/~/\\\n/' posts/arithmetic-made-difficult/*

#-- ADD ME TO THE LIST WHEN I'M LESS NOISY --#
#-- check existence of crossrefs --#
sniff-amd-crossref:VQ:
  CROSS=$( grep '^ & = & ' posts/arithmetic-made-difficult/* || true )
  if [ -z "$CROSS" ]; then
    echo 'Cross references OK' | doppler lightgreen
  else
    echo "$CROSS"
    echo 'Cross references' | doppler lightred
    echo $( echo "$CROSS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- check latex commands against whitelist --#
sniff-amd-latex:VQ:
  echo 'Checking Latex commands' | doppler lightblue
  LATEX=$( cat posts/arithmetic-made-difficult/* \
    | grep -v '^>' \
    | grep -o '\\[a-zA-Z][a-zA-Z]*' \
    | sort \
    | uniq \
    | diff sniff/amd/latex-whitelist.txt - \
    || true )
  if [ -z "$LATEX" ]; then
    echo 'Latex commands OK' | doppler lightgreen
  else
    echo "$LATEX"
    echo 'Latex commands' | doppler lightred
    echo $( echo "$LATEX" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- consistent order of module imports --#
sniff-amd-import:VQ:
  echo 'Checking Import order' | doppler lightblue
  for file in posts/arithmetic-made-difficult/*
  do
    IMPORT=$( cat "$file" \
      | grep '^> import' \
      | grep -v '^> import Prelude' \
      | grep -v '^> import Test\.QuickCheck' \
      | grep -v '^> import Text.Show.Functions' \
      | grep -v '^> import System.Exit' \
      | orderedby --dict sniff/amd/import-list.txt \
      || true )
    if [ "$IMPORT" ]; then
      echo "$file"
      echo "$IMPORT"
      echo 'Import order' | doppler lightred
      echo $( echo "$IMPORT" | wc -l ) 'problems found' | doppler lightred
      FAILED='oh no'
    fi
  done
  if [ "$FAILED" ]; then
    exit 1
  fi
  echo 'Import order OK' | doppler lightgreen

#-- labels are unique --#
sniff-amd-labels:VQ:
  echo 'Checking Unique labels' | doppler lightblue
  LABELS=$( cat posts/arithmetic-made-difficult/* \
    | grep -o '\[\]{#[a-zA-Z-][a-zA-Z-]*}' \
    | sort \
    | uniq -d \
    || true )
  if [ -z "$LABELS" ]; then
    echo 'Unique labels OK' | doppler lightgreen
  else
    echo "$LABELS"
    echo 'Unique labels' | doppler lightred
    echo $( echo "$LABELS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- eqnarray line ends --#
sniff-amd-eqnarray-ends:VQ:
  echo 'Checking Eqnarray line ends' | doppler lightblue
  ENDS=$( awk '/^\$\$\\begin{eqnarray\*}$/{flag=1;print FILENAME ":" FNR}/^\\end{eqnarray\*}\$\$$/{flag=0;print} {if(flag) printf}' \
      posts/arithmetic-made-difficult/* \
    | sed '/^\$\$/s/\\\\/~/g' \
    | sed '/^\$\$/s/[^&~]//g' \
    | sed 'N;s/\n/ /' \
    | grep -v ' \(&&~\)*&&$' \
    || true )
  if [ -z "$ENDS" ]; then
    echo 'Eqnarray line ends OK' | doppler lightgreen
  else
    echo "$ENDS"
    echo 'Eqnarray line ends' | doppler lightred
    echo $( echo "$ENDS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- ADD ME TO THE LIST WHEN I'M LESS NOISY --#
#-- label format --#
sniff-amd-label-format:VQ:
  echo 'Checking Theorem labels' | doppler lightblue
  LABELS=$( awk '/: theorem :/{printf FILENAME ":" FNR " " $0; getline; print;}' \
      posts/arithmetic-made-difficult/* \
    | grep -v ':::::: theorem :::::\[\]{#[a-z][a-zA-Z-]*}\(\[\]{#[a-z][a-zA-Z-]*}\)*$' \
    || true )
  if [ -z "$LABELS" ]; then
    echo 'Theorem labels OK' | doppler lightgreen
  else
    echo "$LABELS"
    echo 'Theorem labels' | doppler lightred
    echo $( echo "$LABELS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi
  
  echo 'Checking Definition labels' | doppler lightblue
  LABELS=$( awk '/: definition :/{printf FILENAME ":" FNR " " $0; getline; print;}' \
      posts/arithmetic-made-difficult/* \
    | grep -v ':::::: definition ::\[\]{#[a-z][a-zA-Z-]*}\(\[\]{#[a-z][a-zA-Z-]*}\)*$' \
    || true )
  if [ -z "$LABELS" ]; then
    echo 'Definition labels OK' | doppler lightgreen
  else
    echo "$LABELS"
    echo 'Definition labels' | doppler lightred
    echo $( echo "$LABELS" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi

#-- test arg order --#
sniff-amd-arg-order:VQ:
  echo 'Checking Test argument order' | doppler lightblue
  ARGORD=$( grep '>   _test_' posts/arithmetic-made-difficult/* \
    | grep -v '_test_[a-zA-Z_]*[ ]*[1-9][0-9]* [1-9][0-9]* ' \
    || true )
  if [ -z "$ARGORD" ]; then
    echo 'Test argument order OK' | doppler lightgreen
  else
    echo "$ARGORD"
    echo 'Test argument order' | doppler lightred
    echo '- number and size arguments should come first' | doppler lightred
    echo $( echo "$ARGORD" | wc -l ) 'problems found' | doppler lightred
    exit 1
  fi
