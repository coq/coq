# 
#	General variables
#

TOPDIR=../../..

# Files with axioms to be realized: can't be extracted directly

AXIOMSVO:= \
theories/Arith/Arith.vo \
theories/Lists/List.vo \
theories/Reals/% \
theories/Num/% \
theories/Relations/Rstar.vo \
theories/Sets/Integers.vo \
theories/ZArith/Zsyntax.vo

DIRS:= $(shell (cd $(TOPDIR);find theories -type d ! -name CVS))

INCL:= $(patsubst %,-I %,$(DIRS))

VO:= $(shell (cd $(TOPDIR);find theories -name \*.vo))

VO:= $(filter-out $(AXIOMSVO),$(VO))

ML:= $(shell test -x v2ml && ./v2ml $(VO))

CMO:= $(patsubst %.ml,%.cmo,$(ML))

#
#	General rules 
#

all: ml $(CMO) v2ml

ml: $(ML)

depend: $(ML)
	rm -f .depend; ocamldep $(INCL) theories/*/*.ml > .depend

tree:
	mkdir -p $(DIRS)

%.cmo:%.ml
	ocamlc $(INCL) -c -i $<

$(ML): ml2v
	./extract `./ml2v $@`

clean: 
	rm -f theories/*/*.ml theories/*/*.cm* theories/*/*.ml.orig


#
#	Extraction of Reals
#

REALSALLVO:=$(shell cd ../../..; ls -tr theories/Reals/*.vo)
REALSVO:=$(filter-out theories/Reals/Rsyntax.vo,$(REALSALLVO))
REALSML:=$(shell test -x v2ml && ./v2ml $(REALSVO))
REALSCMO:= $(patsubst %.ml,%.cmo,$(REALSML))

reals: all $(REALSML) theories/Reals/addReals.cmo $(REALSCMO)

realsml: 
	./extract_reals $(REALSVO)

theories/Reals/addReals.ml: 
	cp -f addReals theories/Reals/addReals.ml

$(REALSML): realsml


#
#	Utilities
#

open: 
	find theories -name "*".ml -exec qualify2open \{\} \;

undo_open: 
	find theories -name "*".ml -exec mv \{\}.orig \{\} \;

ml2v: ml2v.ml
	ocamlc -o $@ $<

v2ml: v2ml.ml
	ocamlc -o $@ $< 
	$(MAKE)


#
#	The End
#

.PHONY: all tree clean reals realsml depend

include .depend



