include ../config/Makefile

LOCALINCLUDES=-I ../config -I ../tools -I ../tools/coqdoc \
	      -I ../scripts -I ../lib -I ../kernel -I ../kernel/byterun -I ../library \
              -I ../proofs -I ../tactics -I ../pretyping \
              -I ../interp -I ../toplevel -I ../parsing -I ../ide/utils -I ../ide \
              -I ../plugins/omega -I ../plugins/romega \
	      -I ../plugins/ring -I ../plugins/dp -I ../plugins/setoid_ring \
              -I ../plugins/xml -I ../plugins/extraction \
              -I ../plugins/fourier -I ../plugins/cc \
	      -I ../plugins/funind -I ../plugins/firstorder \
              -I ../plugins/field -I ../plugins/subtac -I ../plugins/rtauto \
              -I ../plugins/recdef

MLINCLUDES=$(LOCALINCLUDES) -I $(MYCAMLP4LIB)

MLIS=$(wildcard ../lib/*.mli ../kernel/*.mli ../library/*.mli \
	../pretyping/*.mli ../interp/*.mli \
	../parsing/*.mli ../proofs/*.mli \
	../tactics/*.mli ../toplevel/*.mli)

all:: html coq.pdf

newsyntax.dvi: newsyntax.tex
	latex $<
	latex $<

coq.dvi: coq.tex
	latex coq
	latex coq

coq.tex::
	ocamldoc -latex -rectypes -I /usr/lib/ocaml/camlp5 $(MLINCLUDES)\
	$(MLIS) -t "Coq mlis documentation" -intro docintro -o coq.tex

html::
	ocamldoc -html -rectypes -I /usr/lib/ocaml/camlp5 $(MLINCLUDES)\
	$(MLIS) -d html -colorize-code \
	-t "Coq mlis documentation" -intro docintro -css-style style.css

%.dot: ../%
	ocamldoc -rectypes $(MLINCLUDES) -t $* -dot -dot-reduce ../$*/*.ml ../$*/*.mli -o $@

%.png: %.dot
	dot -Tpng $< -o $@

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .png

%.pdf: %.tex
	pdflatex $< && pdflatex $<