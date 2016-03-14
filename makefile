SHELL    = /bin/bash
CLASSDIR = $(HOME)/documents/classes
STHDIR   = $(HOME)/code/st-haskell

all: gather build move
	echo "Successfully built nbloomf.github.io" | doppler lightgreen

site: site.lhs
	ghc --make -threaded site.lhs

build: site
	./site clean
	./site build

watch: FORCE
	echo "View at localhost:8000"
	./site watch

move: FORCE
	cp -r _site/. ../nbloomf.github.io/

gather: FORCE
	# Get frozen class PDFs
	cp -r $(CLASSDIR)/coal/pdf/. pdf/classes/coal
	cp -r $(CLASSDIR)/ring/pdf/. pdf/classes/ring
	cp -r $(CLASSDIR)/geom/pdf/. pdf/classes/geom
	cp -r $(CLASSDIR)/calc/pdf/. pdf/classes/calc
	cp -r $(CLASSDIR)/stat/pdf/. pdf/classes/stat
	cp -r $(CLASSDIR)/prfs/pdf/. pdf/classes/prfs

FORCE:
