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

all: allml .depend allcmo

allml: .names.ml $(MLNAMES)

allcmo: .names.cmo $(CMONAMES)

.depend: Makefile
	rm -f .depend; ocamldep $(INCL) theories/*/*.ml > .depend

.names.ml: Makefile v2ml 
	rm -f .names.ml; \
	echo "MLNAMES= \\" > .names.ml; \
	find theories  -name \*.v -exec ./v2ml \{\} \; | \
	sed -e "s/\.ml/.ml \\\\/" >> .names.ml

.names.cmo: .names.ml
	rm -f .names.cmo; \
	sed -e "1s/ML/CMO/" -e "s/\.ml/.cmo/" < .names.ml > .names.cmo

tree: 
	cp -fur $(TOPDIR)/theories .; rm -f theories/*/*.vo theories/*/*/*.vo


%.cmo:%.ml
	ocamlc $(INCL) -c -i $<

%.ml: ml2v
	./extract `./ml2v $@`

clean: 
	rm -f theories/*/*.ml theories/*/*.cm*

ml2v: ml2v.ml
	ocamlc -o $@ $<

v2ml: v2ml.ml
	ocamlc -o $@ $< 

include .depend
