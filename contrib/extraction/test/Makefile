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

all: $(ML) .depend $(CMO) v2ml

depend: $(ML)
	rm -f .depend; ocamldep $(INCL) $(ML) > .depend

tree:
	mkdir -p $(DIRS)

%.cmo:%.ml
	ocamlc $(INCL) -c -i $<

$(ML): ml2v
	./extract `./ml2v $@`

clean: 
	rm -f theories/*/*.ml theories/*/*.cm*


#
#	Extraction of Reals
#

REALSML:= \
theories/Reals/typeSyntax.ml \
theories/Reals/addReals.ml \
theories/Reals/rdefinitions.ml \
theories/Reals/raxioms.ml \
theories/Reals/r_Ifp.ml \
theories/Reals/rbase.ml \
theories/Reals/rbasic_fun.ml \
theories/Reals/rlimit.ml \
theories/Reals/rderiv.ml

REALSCMO:= $(patsubst %.ml,%.cmo,$(REALSML))

reals: all $(REALSML) $(REALSCMO)

realsml: 
	./extract_reals
	cp -f addReals.ml theories/Reals

$(REALSML): realsml


#
#	Utilities
#

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



