SHELL    = /bin/bash
CLASSDIR = $(HOME)/documents/classes
NOTEDIR  = $(HOME)/documents/notebooks
TEXDIR   = $(HOME)/documents/tex-examples

PATH := $(shell pwd)/_bin:$(PATH)

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
	
	@echo '  software tools docs' | doppler lightmagenta
	@(rm -r pages/sth/* || true) 2> /dev/null


check: FORCE
	@wget -r -nv --spider https://nbloomf.github.io
	@rm -r nbloomf.github.io


tools:
	$(call haskell_exe,2016-02-08-software-tools-in-haskell-noop,sth-noop)
	$(call haskell_exe,2016-02-10-software-tools-in-haskell-copy,sth-copy)
	$(call haskell_exe,2016-02-11-software-tools-in-haskell-count,sth-count)
	$(call haskell_exe,2016-02-12-software-tools-in-haskell-wordcount,sth-wordcount)
	$(call haskell_exe,2016-02-13-software-tools-in-haskell-sentcount,sth-sentcount)
	$(call haskell_exe,2016-02-14-software-tools-in-haskell-glyphcount,sth-glyphcount)
	$(call haskell_exe,2016-02-15-software-tools-in-haskell-detab,sth-detab)
	$(call haskell_exe,2016-02-16-software-tools-in-haskell-charcombine,sth-charcombine)
	$(call haskell_exe,2016-02-17-software-tools-in-haskell-charfullwidth,sth-charfullwidth)
	$(call haskell_exe,2016-02-18-software-tools-in-haskell-entab,sth-entab)
	$(call haskell_exe,2016-02-19-software-tools-in-haskell-echo,sth-echo)
	$(call haskell_exe,2016-02-20-software-tools-in-haskell-overstrike,sth-overstrike)
	$(call haskell_exe,2016-02-21-software-tools-in-haskell-unescape,sth-unescape)
	$(call haskell_exe,2016-02-22-software-tools-in-haskell-escape,sth-escape)
	@echo 'testing...' | doppler lightgreen
	(cd _bin/; shelltest --color --execdir ../test/ -- --threads=16 --hide-successes)

# compile a literate haskell post
define haskell_exe
  @echo "building $(1)" | doppler lightblue
  @cp posts/$(1).lhs _temp/$(2).lhs
  @ghc --make _temp/$(2).lhs
  @rm _temp/$(2).hi _temp/$(2).o _temp/$(2).lhs
  @mv _temp/$(2) _bin/$(2)
endef


FORCE:
