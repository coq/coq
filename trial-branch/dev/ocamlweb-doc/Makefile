
# Makefile for doc/

all:: newparse coq.ps minicop.ps
#newsyntax.dvi minicoq.dvi


OBJS=lex.cmo ast.cmo parse.cmo syntax.cmo

newparse: $(OBJS) syntax.mli lex.ml syntax.ml
	ocamlc -o newparse $(OBJS)

%.cmo: %.ml
	ocamlc -c $<

%.cmi: %.mli
	ocamlc -c $<

%.ml: %.mll
	ocamllex $<

%.ml: %.mly
	ocamlyacc -v $<

%.mli: %.mly
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
	ocamlweb -p "\usepackage{epsfig}" \
	macros.tex intro.tex \
	../../lib/{doc.tex,*.mli} ../../kernel/{doc.tex,*.mli} ../../library/{doc.tex,*.mli} \
	../../pretyping/{doc.tex,*.mli} ../../interp/{doc.tex,*.mli} \
	../../parsing/{doc.tex,*.mli} ../../proofs/{doc.tex,*.mli} \
	../../tactics/{doc.tex,*.mli} ../../toplevel/{doc.tex,*.mli} \
	-o coq.tex


depend:: kernel.dep.ps library.dep.ps pretyping.dep.ps parsing.dep.ps \
         proofs.dep.ps tactics.dep.ps toplevel.dep.ps interp.dep.ps

%.dot: ../%
	(cd ../$*; ocamldep *.ml *.mli) | ocamldot -lr > $@

%.dep.ps: %.dot
	dot -Tps $< -o $@

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps .cmo .cmi .mli .ml .mll .mly

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips $< -o $@


