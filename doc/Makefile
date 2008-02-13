# Makefile for the Coq documentation

# COQSRC needs to be set to a coq source repository

# To compile documentation, you need the following tools:
# Dvi: latex (latex2e), bibtex, makeindex
# Pdf: pdflatex
# Html: hevea (http://hevea.inria.fr) >= 1.05

include ../config/Makefile


LATEX=latex
BIBTEX=bibtex -min-crossrefs=10
MAKEINDEX=makeindex
PDFLATEX=pdflatex

HEVEALIB=/usr/local/lib/hevea:/usr/lib/hevea
export TEXINPUTS=$(COQSRC)/doc:$(HEVEALIB):

COQTOP=$(COQSRC)/bin/coqtop
COQTEX=$(COQSRC)/bin/coq-tex -n 72 -image $(COQTOP) -v -sl -small
COQDOC=$(COQSRC)/bin/coqdoc

#VERSION=POSITIONNEZ-CETTE-VARIABLE

######################################################################
### General rules
######################################################################

all: all-html all-pdf all-ps

all-html:\
  tutorial/Tutorial.v.html refman/html/index.html \
  faq/html/index.html stdlib/html/index.html RecTutorial/RecTutorial.v.html

all-pdf:\
  tutorial/Tutorial.v.pdf refman/Reference-Manual.pdf \
  faq/FAQ.v.pdf stdlib/Library.pdf RecTutorial/RecTutorial.v.pdf

all-ps:\
  tutorial/Tutorial.v.ps refman/Reference-Manual.ps \
  faq/FAQ.v.ps stdlib/Library.ps RecTutorial/RecTutorial.v.ps

refman:\
  refman/html/index.html refman/Reference-Manual.ps refman/Reference-Manual.pdf

tutorial:\
  tutorial/Tutorial.v.html tutorial/Tutorial.v.ps tutorial/Tutorial.v.pdf

stdlib:\
  stdlib/html/index.html stdlib/Library.ps stdlib/Library.pdf

faq:\
  faq/html/index.html faq/FAQ.v.ps faq/FAQ.v.pdf

rectutorial:\
  RecTutorial/RecTutorial.v.html \
  RecTutorial/RecTutorial.v.ps RecTutorial/RecTutorial.v.pdf

######################################################################
### Implicit rules
######################################################################

.SUFFIXES: .dvi .tex .v.tex .ps .pdf .eps .png

%.v.tex: %.tex
	(cd `dirname $<`; $(COQTEX) `basename $<`)

%.ps: %.dvi
	(cd `dirname $<`; dvips -o `basename $@` `basename $<`)

%.eps: %.png
	pngtopnm $< | pnmtops -equalpixels -noturn -rle > $@

clean:
	rm -f */*.dvi */*.aux */*.log */*.bbl */*.blg */*.toc \
	*/*.idx */*~ */*.ilg */*.ind */*.dvi.gz */*.ps.gz */*.pdf.gz\
	*/*.???idx */*.???ind */*.v.tex */*.atoc */*.lof\
	*/*.hatoc */*.haux */*.hcomind */*.herrind */*.hidx */*.hind \
	*/*.htacind */*.htoc */*.v.html
	rm -f stdlib/index-list.html stdlib/index-body.html \
	  stdlib/Library.coqdoc.tex stdlib/library.files \
	  stdlib/library.files.ls
	rm -f stdlib/html/*.html
	rm -f refman/euclid.ml{,i} refman/heapsort.ml{,i}
	rm -f common/version.tex
	rm -f refman/*.eps refman/Reference-Manual.html
	rm -f coq.tex

cleanall: clean
	rm -f */*.ps */*.pdf
	rm -rf refman/html stdlib/html faq/html tutorial/tutorial.v.html

######################################################################
# Common
######################################################################

COMMON=common/version.tex common/title.tex common/macros.tex 

### Version

common/version.tex: Makefile
	echo "\newcommand{\coqversion}{$(VERSION)}" > common/version.tex

######################################################################
# Reference Manual
######################################################################

REFMANCOQTEXFILES=\
  refman/RefMan-gal.v.tex refman/RefMan-ext.v.tex \
  refman/RefMan-mod.v.tex refman/RefMan-tac.v.tex \
  refman/RefMan-cic.v.tex refman/RefMan-lib.v.tex \
  refman/RefMan-tacex.v.tex refman/RefMan-syn.v.tex \
  refman/RefMan-oth.v.tex refman/RefMan-ltac.v.tex \
  refman/RefMan-decl.v.tex \
  refman/Cases.v.tex refman/Coercion.v.tex refman/Extraction.v.tex \
  refman/Program.v.tex refman/Omega.v.tex refman/Polynom.v.tex \
  refman/Setoid.v.tex refman/Helm.tex # refman/Natural.v.tex

REFMANTEXFILES=\
  refman/headers.sty \
  refman/Reference-Manual.tex refman/RefMan-pre.tex \
  refman/RefMan-int.tex refman/RefMan-pro.tex \
  refman/RefMan-com.tex \
  refman/RefMan-uti.tex refman/RefMan-ide.tex \
  refman/RefMan-add.tex refman/RefMan-modr.tex \
  $(REFMANCOQTEXFILES) \

REFMANEPSFILES= refman/coqide.eps refman/coqide-queries.eps

REFMANFILES=\
  $(REFMANTEXFILES) $(COMMON) $(REFMANEPSFILES) refman/biblio.bib

REFMANPNGFILES=$(REFMANEPSFILES:.eps=.png)

### Reference Manual (printable format)

# The second LATEX compilation is necessary otherwise the pages of the index
# are not correct (don't know why...) - BB
refman/Reference-Manual.dvi: $(REFMANFILES)
	(cd refman;\
	$(LATEX) Reference-Manual;\
	$(BIBTEX) Reference-Manual;\
	$(LATEX) Reference-Manual;\
	$(MAKEINDEX) Reference-Manual;\
	$(MAKEINDEX) Reference-Manual.tacidx -o Reference-Manual.tacind;\
	$(MAKEINDEX) Reference-Manual.comidx -o Reference-Manual.comind;\
	$(MAKEINDEX) Reference-Manual.erridx -o Reference-Manual.errind;\
	$(LATEX) Reference-Manual;\
	$(LATEX) Reference-Manual)

refman/Reference-Manual.pdf: refman/Reference-Manual.tex
	(cd refman; $(PDFLATEX) Reference-Manual.tex)

### Reference Manual (browsable format)

refman/Reference-Manual.html: refman/headers.hva refman/Reference-Manual.dvi # to ensure bbl file
	(cd refman; hevea -fix -exec xxdate.exe ./Reference-Manual.tex)

refman/html/index.html: refman/Reference-Manual.html $(REFMANPNGFILES) \
                        refman/cover.html refman/index.html
	- rm -rf refman/html
	mkdir refman/html
	cp $(REFMANPNGFILES) refman/html
	(cd refman/html; hacha -o toc.html ../Reference-Manual.html)
	cp refman/cover.html refman/menu.html refman/html
	cp refman/index.html refman/html

refman-quick:
	(cd refman; \
	 $(PDFLATEX) Reference-Manual.tex; \
	 hevea -fix -exec xxdate.exe ./Reference-Manual.tex)


######################################################################
# Tutorial
######################################################################

tutorial/Tutorial.v.dvi: common/version.tex common/title.tex tutorial/Tutorial.v.tex
	(cd tutorial; $(LATEX) Tutorial.v)

tutorial/Tutorial.v.pdf: common/version.tex common/title.tex tutorial/Tutorial.v.dvi
	(cd tutorial; $(PDFLATEX) Tutorial.v.tex)

tutorial/Tutorial.v.html: tutorial/Tutorial.v.tex
	(cd tutorial; hevea -exec xxdate.exe Tutorial.v)


######################################################################
# FAQ
######################################################################

faq/FAQ.v.dvi: common/version.tex common/title.tex faq/FAQ.v.tex
	(cd faq;\
	$(LATEX) FAQ.v;\
	$(BIBTEX) FAQ.v;\
	$(LATEX) FAQ.v;\
	$(LATEX) FAQ.v)

faq/FAQ.v.pdf: common/version.tex common/title.tex faq/FAQ.v.dvi faq/axioms.png
	(cd faq; $(PDFLATEX) FAQ.v.tex)

faq/FAQ.v.html: faq/FAQ.v.dvi # to ensure FAQ.v.bbl
	(cd faq; hevea -fix FAQ.v.tex)

faq/html/index.html: faq/FAQ.v.html
	- rm -rf faq/html
	mkdir faq/html
	cp faq/interval_discr.v faq/axioms.png faq/html
	cp faq/FAQ.v.html faq/html/index.html

######################################################################
# Standard library
######################################################################

LIBDIRS= Init Logic Bool Arith NArith ZArith QArith Relations Sets Setoids Lists Sorting Wellfounded IntMap FSets Reals Program
# We avoid Strings as String.v contains unicode caracters that make latex fail

LIBDIRS+= Ints Ints/num Ints/Z
LIBDIRS+= Numbers Numbers/NatInt Numbers/Natural/Abstract Numbers/Natural/Binary Numbers/Natural/Peano Numbers/Integer/Abstract Numbers/Integer/NatPairs Numbers/Integer/Binary


ALLTHEORIES_VO=$(foreach dir, $(LIBDIRS), $(wildcard $(COQSRC)/theories/$(dir)/*.vo))
ALLTHEORIES_V=$(ALLTHEORIES_VO:%.vo=%.v)
ALLTHEORIES_GLOB = $(ALLTHEORIES_V:%.v=%.glob)

### Standard library (browsable html format)

stdlib/index-body.html: $(ALLTHEORIES_V)
	- rm -rf stdlib/html
	mkdir stdlib/html
	(cd stdlib/html;\
	 $(COQDOC) -q --multi-index --html \
	  -R $(COQSRC)/theories Coq $(ALLTHEORIES_V))
	mv stdlib/html/index.html stdlib/index-body.html

stdlib/index-list.html: stdlib/index-list.html.template
	COQTOP=$(COQSRC) ./stdlib/make-library-index stdlib/index-list.html

stdlib/html/index.html: stdlib/index-list.html stdlib/index-body.html stdlib/index-trailer.html
	cat stdlib/index-list.html > $@
	sed -n -e '/<table>/,/<\/table>/p' stdlib/index-body.html >> $@
	cat stdlib/index-trailer.html >> $@

### Standard library (printable format - produces > 350 pages)

stdlib/Library.coqdoc.tex: 
	(for dir in $(LIBDIRS) ; do \
	  $(COQDOC) -q --gallina --body-only --latex --stdout \
	    --coqlib_path $(COQSRC) \
            -R $(COQSRC)/theories Coq "$(COQSRC)/theories/$$dir/"*.v >> $@ ; done)

stdlib/Library.dvi: $(COMMON) stdlib/Library.coqdoc.tex stdlib/Library.tex
	(cd stdlib;\
	$(LATEX) Library;\
	$(LATEX) Library)

stdlib/Library.pdf: $(COMMON) stdlib/Library.coqdoc.tex stdlib/Library.dvi
	(cd stdlib; $(PDFLATEX) Library)

######################################################################
# Tutorial on inductive types
######################################################################

RecTutorial/RecTutorial.v.dvi: common/version.tex common/title.tex RecTutorial/RecTutorial.v.tex
	(cd RecTutorial;\
	 $(LATEX) RecTutorial.v;\
	 $(BIBTEX) RecTutorial.v;\
	 $(LATEX) RecTutorial.v;\
	 $(LATEX) RecTutorial.v)

RecTutorial/RecTutorial.v.pdf: common/version.tex common/title.tex RecTutorial/RecTutorial.v.dvi
	(cd RecTutorial; $(PDFLATEX) RecTutorial.v.tex)

RecTutorial/RecTutorial.v.html: RecTutorial/RecTutorial.v.tex
	(cd RecTutorial; hevea -exec xxdate.exe RecTutorial.v)


######################################################################
# Install all documentation files
######################################################################

COQINSTALLPREFIX=
DOCDIR=/usr/local/share/doc/coq-8.0
FULLDOCDIR=$(COQINSTALLPREFIX)$(DOCDIR)
HTMLINSTALLDIR=$(FULLDOCDIR)/html
PRINTABLEINSTALLDIR=$(FULLDOCDIR)/ps

install-doc: install-meta install-doc-html install-doc-printable

install-meta:
	mkdir $(DOCDIC)
	cp LICENCE $(DOCDIC)/LICENCE.doc
#	cp $(COQSRC)/LICENCE $(COQTOP)/CREDITS $(COQSRC)/COPYRIGHT $(DOCDIC)
#	cp $(COQSRC)/README $(COQSRC)/CHANGES $(DOCDIC)

install-doc-html: all-html
	mkdir $(HTMLINSTALLDIR)
	cp -r refman/html $(HTMLINSTALLDIR)/refman
	cp -r stdlib/html $(HTMLINSTALLDIR)/stdlib
	cp -r tutorial/tutorial.html $(HTMLINSTALLDIR)/
	cp -r RecTutorial/RecTutorial.html $(HTMLINSTALLDIR)/
	cp -r faq/html $(HTMLINSTALLDIR)/faq

install-doc-printable: all-pdf all-ps
	mkdir $(PRINTABLEINSTALLDIR)
	cp -r refman/Reference-manual.pdf $(PRINTABLEINSTALLDIR)
	cp -r stdlib/Library.pdf $(PRINTABLEINSTALLDIR)
	cp -r tutorial/Tutorial.v.pdf $(PRINTABLEINSTALLDIR)/Tutorial.pdf
	cp -r RecTutorial/RecTutorial.v.pdf $(PRINTABLEINSTALLDIR)/RecTutorial.pdf
	cp -r faq/FAQ.v.pdf $(PRINTABLEINSTALLDIR)/FAQ.pdf
	cp -r refman/Reference-manual.ps $(PRINTABLEINSTALLDIR)
	cp -r stdlib/Library.ps $(PRINTABLEINSTALLDIR)
	cp -r tutorial/Tutorial.v.ps $(PRINTABLEINSTALLDIR)/Tutorial.ps
	cp -r RecTutorial/RecTutorial.v.ps $(PRINTABLEINSTALLDIR)/RecTutorial.ps
	cp -r faq/FAQ.v.ps $(PRINTABLEINSTALLDIR)/FAQ.ps
