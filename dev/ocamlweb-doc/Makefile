include ../../config/Makefile

LOCALINCLUDES=-I ../../config -I ../../tools -I ../../tools/coqdoc \
	      -I ../../scripts -I ../../lib -I ../../kernel -I ../../kernel/byterun -I ../../library \
              -I ../../proofs -I ../../tactics -I ../../pretyping \
              -I ../../interp -I ../../toplevel -I ../../parsing -I ../../ide/utils -I ../../ide \
              -I ../../contrib/omega -I ../../contrib/romega \
	      -I ../../contrib/ring -I ../../contrib/dp -I ../../contrib/setoid_ring \
              -I ../../contrib/xml -I ../../contrib/extraction \
              -I ../../contrib/interface -I ../../contrib/fourier \
	      -I ../../contrib/jprover -I ../../contrib/cc \
	      -I ../../contrib/funind -I ../../contrib/firstorder \
              -I ../../contrib/field -I ../../contrib/subtac -I ../../contrib/rtauto \
              -I ../../contrib/recdef

MLINCLUDES=$(LOCALINCLUDES) -I $(MYCAMLP4LIB)


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

%.dot: ../../%
	ocamldoc -rectypes $(MLINCLUDES) -t $* -dot -dot-reduce ../../$*/*.ml ../../$*/*.mli -o $@

%.dep.ps: %.dot
	dot -Tps $< -o $@

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps .cmo .cmi .mli .ml .mll .mly

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips $< -o $@


