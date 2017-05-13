SHELL = /bin/bash

PATH := $(shell pwd)/_bin/sth:$(shell pwd)/_bin/amd:$(PATH)

targets: FORCE
	@echo 'watch    : serve pages locally'           | doppler lightcyan
	@echo 'build    : generate nbloomf.github.io'    | doppler lightcyan
	@echo 'site     : compile site'                  | doppler lightcyan
	@echo 'literate : compile literate posts'        | doppler lightcyan
	@echo 'favicons : generate favicons'             | doppler lightcyan
	@echo 'winfiles : convert raw file line endings' | doppler lightcyan



#=====================#
# serve pages locally #
#=====================#

watch: site FORCE
	@echo 'View at localhost:8000' | doppler lightcyan
	./site watch


build: site favicons winfiles FORCE
	./site clean
	./site build
	@cp -r _site/. ../nbloomf.github.io/
	@echo "built nbloomf.github.io" | doppler lightgreen


site: site.lhs
	@ghc --make -threaded site.lhs
	@rm site.o site.hi

check: FORCE
	@wget -r -nv --spider https://nbloomf.github.io
	@rm -r nbloomf.github.io



#===================#
# generate favicons #
#===================#

favicons:              \
  raw/gfx/icon/favicon-32.png  \
  raw/gfx/icon/favicon-57.png  \
  raw/gfx/icon/favicon-114.png \
  raw/gfx/icon/favicon-152.png
	@echo "generated favicons" | doppler lightgreen

raw/gfx/icon/favicon-32.png: raw/gfx/icon/info.svg
	@echo "generating favicon-32" | doppler lightblue
	@inkscape -z -e $@ -w 32 -h 32 $<

raw/gfx/icon/favicon-57.png: raw/gfx/icon/info.svg
	@echo "generating favicon-57" | doppler lightblue
	@inkscape -z -e $@ -w 57 -h 57 $<

raw/gfx/icon/favicon-114.png: raw/gfx/icon/info.svg
	@echo "generating favicon-114" | doppler lightblue
	@inkscape -z -e $@ -w 114 -h 114 $<

raw/gfx/icon/favicon-152.png: raw/gfx/icon/info.svg
	@echo "generating favicon-152" | doppler lightblue
	@inkscape -z -e $@ -w 152 -h 152 $<



#======================#
# convert line endings #
#======================#

winfiles: $(shell find raw/tex/win/ -type f)
	@echo "converted raw text to win line endings" | doppler lightgreen

raw/tex/win/%: raw/tex/unix/%
	@echo "converting $<" | doppler lightblue
	@cat $< | awk '{ sub("$$", "\r"); print }' > $@



#========================#
# compile literate posts #
#========================#

literate: sth amd


# software tools in haskell #

sth: sth-exe
	@echo "testing sth..." | doppler lightblue
	@(shelltest --color --execdir test/sth -- --threads=16)

sth-exe: FORCE
	@echo "building sth..." | doppler lightblue
	@(cd posts/software-tools-in-haskell; cabal install)
	$(call sth_move,noop)
	$(call sth_move,copy)
	$(call sth_move,count)
	$(call sth_move,wordcount)
	$(call sth_move,sentcount)
	$(call sth_move,glyphcount)
	$(call sth_move,detab)
	$(call sth_move,charcombine)
	$(call sth_move,charfullwidth)
	$(call sth_move,entab)
	$(call sth_move,echo)
	$(call sth_move,overstrike)
	$(call sth_move,unescape)
	$(call sth_move,escape)
	$(call sth_move,compress)
	$(call sth_move,expand)
	$(call sth_move,crypt)
	$(call sth_move,translit)
	$(call sth_move,charreplace)
	$(call sth_move,tail)
	$(call sth_move,getlines)
	$(call sth_move,compare)
	$(call sth_move,import)
	$(call sth_move,concat)
	$(call sth_move,wye)
	$(call sth_move,pslineprint)
	$(call sth_move,paginate)
	$(call sth_move,examine)
	$(call sth_move,archive)
	$(call sth_move,linenumber)
	$(call sth_move,bubble)

# move a software tools in haskell exe
define sth_move
  @echo "moving $(1)" | doppler lightgreen
  @mv posts/software-tools-in-haskell/dist/build/sth-$(1)/sth-$(1) _bin/sth
endef


# arithmetic made difficult #

amd: amd-exe
	@echo "testing amd..." | doppler lightblue
	@(shelltest --color --execdir test/amd -- --threads=16)

amd-exe: FORCE
	@echo "building amd..." | doppler lightblue
	@(cd posts/arithmetic-made-difficult; cabal install)
	$(call amd_move,boolean)
	$(call amd_move,nat)
	$(call amd_move,plus)
	$(call amd_move,times)
	$(call amd_move,minus)
	$(call amd_move,leq)
	$(call amd_move,max-min)
	$(call amd_move,divalg)
	$(call amd_move,div)
	$(call amd_move,gcd)
	$(call amd_move,coprime)
	$(call amd_move,lcm)
	$(call amd_move,prime)
	$(call amd_move,power)
	$(call amd_move,rev)
	$(call amd_move,cat)
	$(call amd_move,length)
	$(call amd_move,at)
	$(call amd_move,map)
	$(call amd_move,range)
	$(call amd_move,zip)
	$(call amd_move,unzip)
	$(call amd_move,prefix)
	$(call amd_move,lcp)
	$(call amd_move,all-any)
	$(call amd_move,tails-inits)
	$(call amd_move,filter)

# move an arithmetic made difficult exe
define amd_move
  @echo "moving $(1)" | doppler lightgreen
  @mv posts/arithmetic-made-difficult/dist/build/amd-$(1)/amd-$(1) _bin/amd
endef


FORCE:
