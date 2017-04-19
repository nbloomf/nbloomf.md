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



#---------------------------#
# software tools in haskell #
#---------------------------#

sth:
	$(call software_tools_exe,noop)
	$(call software_tools_exe,copy)
	$(call software_tools_exe,count)
	$(call software_tools_exe,wordcount)
	$(call software_tools_exe,sentcount)
	$(call software_tools_exe,glyphcount)
	$(call software_tools_exe,detab)
	$(call software_tools_exe,charcombine)
	$(call software_tools_exe,charfullwidth)
	$(call software_tools_exe,entab)
	$(call software_tools_exe,echo)
	$(call software_tools_exe,overstrike)
	$(call software_tools_exe,unescape)
	$(call software_tools_exe,escape)
	$(call software_tools_exe,compress)
	$(call software_tools_exe,expand)
	$(call software_tools_exe,crypt)
	$(call software_tools_exe,translit)
	$(call software_tools_exe,charreplace)
	$(call software_tools_exe,tail)
	$(call software_tools_exe,getlines)
	$(call software_tools_exe,compare)
	$(call software_tools_exe,import)
	$(call software_tools_exe,concat)
	$(call software_tools_exe,wye)
	$(call software_tools_exe,pslineprint)
	$(call software_tools_exe,paginate)
	$(call software_tools_exe,examine)
	$(call software_tools_exe,archive)
	$(call software_tools_exe,linenumber)
	$(call software_tools_exe,bubble)
	@echo 'testing...' | doppler lightgreen
	@(shelltest --color --execdir test/sth -- --threads=16 --hide-successes)

# compile a literate haskell post
# $(1) is the source file path sans name
# $(2) is the source file name sans extension
# $(3) is the desired executable name
# $(4) is the target path inside _bin
define haskell_exe
  @echo "building $(1)/$(2)" | doppler lightblue
  @cp posts/$(1)/$(2).lhs _temp/$(3).lhs
  @cp -R posts/$(1)/Lib _temp/Lib
  @(cd _temp/; ghc -O2 --make $(3).lhs)
  @rm -r _temp/$(3).hi _temp/$(3).o _temp/$(3).lhs _temp/Lib
  @mv _temp/$(3) _bin/$(4)/$(3)
endef

# compile a software tools post
define software_tools_exe
  $(call haskell_exe,software-tools-in-haskell,$(1),sth-$(1),sth)
endef



#---------------------------#
# arithmetic made difficult #
#---------------------------#

amd: FORCE
	@(cd posts/arithmetic-made-difficult; cabal install)
	$(call amd_move,plus)
	$(call amd_move,times)
	$(call amd_move,minus)
	@rm -rf posts/arithmetic-made-difficult/dist
	@(shelltest --color --execdir test/amd -- --threads=16 --hide-successes)

# move an arithmetic made difficult exe
define amd_move
  @echo "moving $(1)" | doppler lightblue
  @mv posts/arithmetic-made-difficult/dist/build/amd-$(1)/amd-$(1) _bin/amd
endef


FORCE:

.PHONY: amd
