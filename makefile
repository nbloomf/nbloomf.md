site: FORCE
	ghc --make -threaded site.hs
	./site clean
	./site build

build: FORCE
	./site clean
	./site build

watch: FORCE
	echo "View at localhost:8000"
	./site watch

move: FORCE
	cp -r _site/* ../nbloomf.github.io/

FORCE:
