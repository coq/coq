
# Makefile for doc/

all: minicoq.dvi

coq.dvi: coq.tex
	latex coq && latex coq

clean::
	rm -f *~ *.log *.aux

.SUFFIXES: .tex .dvi .ps

.tex.dvi:
	latex $< && latex $<

.dvi.ps:
	dvips $< -o
