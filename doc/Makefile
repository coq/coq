
# Makefile for doc/

coq.dvi: coq.tex
	latex coq && latex coq

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps

.dvi.ps:
	dvips $< -o
