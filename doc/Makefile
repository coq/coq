
# Makefile for doc/

all:: newparse 
#newsyntax.dvi minicoq.dvi


OBJS=lex.cmo ast.cmo parse.cmo syntax.cmo

newparse: $(OBJS) syntax.mli lex.ml syntax.ml
	ocamlc -o newparse $(OBJS)

.ml.cmo:
	ocamlc -c $<

.mli.cmi:
	ocamlc -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	ocamlyacc -v $<

.mly.mli:
	ocamlyacc -v $<

clean::
	rm -f *.cm* *.output syntax.ml syntax.mli lex.ml newparse

parse.cmo: ast.cmo
syntax.cmi: parse.cmo
syntax.cmo: lex.cmo parse.cmo syntax.cmi
lex.cmo: syntax.cmi
ast.cmo: ast.ml

newsyntax.dvi: newsyntax.tex
	latex $<
	latex $<

coq.dvi: coq.tex
	latex coq
	latex coq

coq.tex::
	make -C .. doc/coq.tex

depend:: kernel.dep.ps library.dep.ps pretyping.dep.ps parsing.dep.ps \
         proofs.dep.ps tactics.dep.ps toplevel.dep.ps interp.dep.ps

%.dot: ../%
	(cd ../$*; ocamldep *.ml *.mli) | ocamldot -lr > $@

%.dep.ps: %.dot
	dot -Tps $< -o $@

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps .cmo .cmi .mli .ml .mll .mly

.tex.dvi:
	latex $< && latex $<

.dvi.ps:
	dvips $< -o $@

