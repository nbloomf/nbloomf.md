SHELL    = /bin/bash
CLASSDIR = $(HOME)/documents/classes
NOTEDIR  = $(HOME)/documents/notebooks
TEXDIR   = $(HOME)/documents/tex-examples

PATH := $(shell pwd)/_bin/sth:$(shell pwd)/_bin/amd:$(PATH)

all: move FORCE
	@echo "built nbloomf.github.io" | doppler lightgreen

site: site.lhs
	@ghc --make -threaded site.lhs

build: site gather FORCE
	./site clean
	./site build

watch: FORCE
	@echo 'View at localhost:8000' | doppler lightcyan
	./site watch

move: build FORCE
	@cp -r _site/. ../nbloomf.github.io/

gather: FORCE
	@echo 'generating icons' | doppler lightgreen
	@inkscape -z -e icon/favicon-32.png  -w 32  -h 32  icon/info.svg
	@inkscape -z -e icon/favicon-57.png  -w 57  -h 57  icon/info.svg
	@inkscape -z -e icon/favicon-114.png -w 114 -h 114 icon/info.svg
	@inkscape -z -e icon/favicon-152.png -w 152 -h 152 icon/info.svg
	
	@echo 'gathering documents' | doppler lightgreen
	@echo '  class pdfs' | doppler lightmagenta
	@cp -r $(CLASSDIR)/coal/pdf/. pdf/classes/coal
	@cp -r $(CLASSDIR)/ring/pdf/. pdf/classes/ring
	@cp -r $(CLASSDIR)/geom/pdf/. pdf/classes/geom
	@cp -r $(CLASSDIR)/calc/pdf/. pdf/classes/calc
	@cp -r $(CLASSDIR)/stat/pdf/. pdf/classes/stat
	@cp -r $(CLASSDIR)/prfs/pdf/. pdf/classes/prfs
	@cp -r $(CLASSDIR)/ssem/pdf/. pdf/classes/ssem
	@cp -r $(CLASSDIR)/parp/pdf/. pdf/classes/parp
	
	@echo '  notebooks' | doppler lightmagenta
	@cp $(NOTEDIR)/rings.pdf pdf/notes
	@cp $(NOTEDIR)/geo.pdf pdf/notes
	@cp $(NOTEDIR)/groups.pdf pdf/notes
	
	@echo '  tex examples' | doppler lightmagenta
	@cp -r $(TEXDIR)/md/.  pages/tex-examples
	@cp -r $(TEXDIR)/pdf/. pdf/tex-examples
	@cp -r $(TEXDIR)/gfx/. images/tex-examples
	@cp -r $(TEXDIR)/tex/. raw/tex-examples/unix
	@for f in $(wildcard raw/tex-examples/unix/*); do \
	  cat $$f | awk '{ sub("$$", "\r"); print }' > $${f/unix/win}; \
	done

clean: FORCE
	@echo 'delete generated files' | doppler lightgreen
	@echo '  class pdfs' | doppler lightmagenta
	@(rm pdf/classes/coal/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/ring/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/geom/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/calc/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/stat/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/prfs/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/ssem/*.pdf || true) 2> /dev/null
	@(rm pdf/classes/parp/*.pdf || true) 2> /dev/null


check: FORCE
	@wget -r -nv --spider https://nbloomf.github.io
	@rm -r nbloomf.github.io



#----------------#
# literate posts #
#----------------#

literate: sth amd



#---------------------------#
# software tools in haskell #
#---------------------------#

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
	@rm -rf posts/software-tools-in-haskell/dist

# move an arithmetic made difficult exe
define sth_move
  @echo "moving $(1)" | doppler lightgreen
  @mv posts/software-tools-in-haskell/dist/build/sth-$(1)/sth-$(1) _bin/sth
endef



#---------------------------#
# arithmetic made difficult #
#---------------------------#

amd: amd-exe
	@echo "testing amd..." | doppler lightblue
	@(shelltest --color --execdir test/amd -- --threads=16)

amd-exe: FORCE
	@echo "building amd..." | doppler lightblue
	@(cd posts/arithmetic-made-difficult; cabal install)
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
	@rm -rf posts/arithmetic-made-difficult/dist

# move an arithmetic made difficult exe
define amd_move
  @echo "moving $(1)" | doppler lightgreen
  @mv posts/arithmetic-made-difficult/dist/build/amd-$(1)/amd-$(1) _bin/amd
endef


FORCE:

.PHONY: amd
