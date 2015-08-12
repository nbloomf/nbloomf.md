site: FORCE
	ghc --make -threaded site.hs
	./site build

build: FORCE
	./site build

watch: FORCE
	echo "View at localhost:8000"
	./site watch

move: FORCE
	cp -r _site/* ../nbloomf.github.io/

FORCE:
