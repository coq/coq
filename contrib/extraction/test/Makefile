TOPDIR=../../..

INCL= -I theories/Arith \
-I theories/Bool \
-I theories/Init \
-I theories/IntMap \
-I theories/Lists \
-I theories/Logic \
-I theories/Reals \
-I theories/Relations \
-I theories/Sets \
-I theories/Wellfounded \
-I theories/Zarith


MLNAMES=
CMONAMES=

include .names.ml
include .names.cmo

all: ml2v v2ml allml .depend allcmo

allml: .names.ml $(MLNAMES)

allcmo: .names.cmo $(CMONAMES)

.depend: Makefile
	rm -f .depend; ocamldep $(INCL) theories/*/*.ml > .depend

.names.ml: Makefile v2ml 
	rm -f .names.ml; \
	echo "MLNAMES= \\" > .names.ml; \
	V2ML=`pwd`/v2ml; \
	(cd $(TOPDIR); find theories  -name \*.v -exec $$V2ML \{\} \;) | \
	sed -e "s/\.ml/.ml \\\\/" >> .names.ml

.names.cmo: .names.ml
	rm -f .names.cmo; \
	sed -e "1s/ML/CMO/" -e "s/\.ml/.cmo/" < .names.ml > .names.cmo

tree:
	for f in `cd $(TOPDIR); find theories -type d ! -name CVS`; do \
		mkdir -p $$f; \
	done

ml2v: ml2v.ml
	ocamlc -o $@ $<

v2ml: v2ml.ml
	ocamlc -o $@ $< 

%.cmo:%.ml
	ocamlc $(INCL) -c -i $<

%.ml: 
	./extract `./ml2v $@`

clean: 
	rm -f theories/*/*.ml theories/*/*.cm*

include .depend
