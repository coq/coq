
# Makefile for doc/

all: newsyntax.dvi minicoq.dvi

newsyntax.dvi: newsyntax.tex
	latex $<
	latex $<

coq.dvi: coq.tex
	latex coq
	latex coq

coq.tex::
	make -C .. doc/coq.tex

depend:: kernel.dep.ps library.dep.ps pretyping.dep.ps parsing.dep.ps \
         proofs.dep.ps tactics.dep.ps toplevel.dep.ps

%.dot: ../%
	(cd ../$*; ocamldep *.ml *.mli) | ocamldot -lr > $@

%.dep.ps: %.dot
	dot -Tps $< -o $@

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps

.tex.dvi:
	latex $< && latex $<

.dvi.ps:
	dvips $< -o $@

