# 
#	General variables
#

TOPDIR=../../..

# Files with axioms to be realized: can't be extracted directly

AXIOMSVO:= \
theories/Arith/Arith.vo \
theories/Lists/List.vo \
theories/Reals/% \
theories/Reals/Rsyntax.vo \
theories/Num/% \
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

all: v2ml ml $(CMO)

ml: $(ML)

depend: $(ML)
	rm -f .depend; ocamldep $(INCL) theories/*/*.ml > .depend

tree:
	mkdir -p $(DIRS)

%.cmo:%.ml
	ocamlc $(INCL) -c -i $<

$(ML): ml2v
	./extract $@

clean: 
	rm -f theories/*/*.ml theories/*/*.cm* theories/*/*.ml.orig


#
#	Utilities
#

open: 
	find theories -name "*".ml -exec ./qualify2open \{\} \;

undo_open: 
	find theories -name "*".ml -exec mv \{\}.orig \{\} \;

ml2v: ml2v.ml
	ocamlc -o $@ $<

v2ml: v2ml.ml
	ocamlc -o $@ $< 
	$(MAKE)

#
#	Extraction of Reals
#


REALSAXIOMSVO:=theories/Reals/Rsyntax.vo

REALSALLVO:=$(shell cd $(TOPDIR); ls -tr theories/Reals/*.vo)
REALSVO:=$(filter-out $(REALSAXIOMSVO),$(REALSALLVO))
REALSML:=$(shell test -x v2ml && ./v2ml $(REALSVO))
REALSCMO:= $(patsubst %.ml,%.cmo,$(REALSML))

reals: all realsml theories/Reals/addReals.cmo $(REALSCMO)

realsml: $(REALSML)

theories/Reals/addReals.ml: 
	cp -f addReals theories/Reals/addReals.ml

$(REALSML): 
	./extract $@


#
#	The End
#

.PHONY: all tree clean reals realsml depend

include .depend



