SHELL    = /bin/bash
CLASSDIR = $(HOME)/documents/classes
NOTEDIR  = $(HOME)/documents/notebooks
TEXDIR   = $(HOME)/documents/tex-examples
STHDIR   = $(HOME)/code/st-haskell

all: gather build move
	@echo "built nbloomf.github.io" | doppler lightgreen

site: FORCE
	@ghc --make -threaded site.lhs

build: site
	./site clean
	./site build

watch: FORCE
	@echo 'View at localhost:8000' | doppler lightcyan
	./site watch

move: FORCE
	@cp -r _site/. ../nbloomf.github.io/

gather: FORCE
	@echo 'gathering documents' | doppler lightgreen
	@echo '  class pdfs' | doppler lightmagenta
	@cp -r $(CLASSDIR)/coal/pdf/. pdf/classes/coal
	@cp -r $(CLASSDIR)/ring/pdf/. pdf/classes/ring
	@cp -r $(CLASSDIR)/geom/pdf/. pdf/classes/geom
	@cp -r $(CLASSDIR)/calc/pdf/. pdf/classes/calc
	@cp -r $(CLASSDIR)/stat/pdf/. pdf/classes/stat
	@cp -r $(CLASSDIR)/prfs/pdf/. pdf/classes/prfs
	@cp -r $(CLASSDIR)/ssem/pdf/. pdf/classes/ssem
	
	@echo '  notebooks' | doppler lightmagenta
	@cp $(NOTEDIR)/rings.pdf pdf/notes
	@cp $(NOTEDIR)/geo.pdf pdf/notes
	
	@echo '  software tools' | doppler lightmagenta
	@cp -r $(STHDIR)/gen/doc/. pages/sth
	
	@echo '  tex examples' | doppler lightmagenta
	@cp -r $(TEXDIR)/md/.  pages/tex-examples
	@cp -r $(TEXDIR)/pdf/. pdf/tex-examples
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
	
	@echo '  software tools docs' | doppler lightmagenta
	@(rm -r pages/sth/* || true) 2> /dev/null

FORCE:
