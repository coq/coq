# Makefile for the Coq documentation

# You need the environment variables COQTOP and COQBIN to be correctly set
# (some files are preprocessed using Coq and some part of the documentation
# is automatically built from the theories sources)

# To compile documentation, you need the following tools:
# Dvi: latex (latex2e), bibtex, makeindex, dviselect (package RPM dviutils)
# Ps: dvips, psutils (ftp://ftp.dcs.ed.ac.uk/pub/ajcd/psutils.tar.gz)
# Pdf: pdflatex
# Html:
#   - hevea: http://para.inria.fr/~maranget/hevea/
#   - htmlSplit: http://coq.inria.fr/~delahaye
# Rapports INRIA: dviselect, rrkit (par Michel Mauny)

DOCCOQTOP=$(COQBIN)/coqtop.byte
DOCCOQC=$(COQBIN)/coqc
COQTEX=$(COQBIN)/coq-tex -image $(DOCCOQTOP) -v -sl -small
COQWEBSTY=$(HOME)/tex/inputs

LATEX=latex
BIBTEX=bibtex
MAKEINDEX=makeindex
PDFLATEX=pdflatex

TEST=test

TEXINPUTS=/usr/local/lib/rrkit/RRINPUTSDIR:$(COQWEBSTY):.:

INPUTS=./macros.tex ./title.tex ./headers.tex ./Reference-Manual.tex

LIBFILES=library/Logic.tex library/Datatypes.tex library/Peano.tex \
         library/Wf.tex library/Specif.tex

REFMANCOQTEXFILES=\
  RefMan-gal.v.tex RefMan-ext.v.tex RefMan-tac.v.tex \
  RefMan-cic.v.tex RefMan-lib.v.tex RefMan-tacex.v.tex \
  RefMan-syn.v.tex RefMan-ltac.v.tex RefMan-oth.v.tex

COQTEXFILES= Cases.v.tex Coercion.v.tex Extraction.v.tex Program.v.tex\
  Omega.v.tex Natural.v.tex Changes.v.tex Tutorial.v.tex Polynom.v.tex \
  Correctness.v.tex

REFMANFILES= Reference-Manual.tex RefMan-pre.tex RefMan-int.tex \
  RefMan-pro.tex RefMan-com.tex RefMan-uti.tex RefMan-add.tex \
  $(REFMANCOQTEXFILES) 

REFMAN=Reference-Manual

#VERSION=V6.3.1
VERSION=POSITIONNEZ-CETTE-VARIABLE
FTPDOCDIR=/net/pauillac/infosystems/ftp/coq/coq/$(VERSION)/doc
WWWDOCDIR=/net/pauillac/infosystems/www/coq/doc

FTPDOCS=Changes.dvi.gz Changes.ps.gz \
        Reference-Manual-base.ps.gz Reference-Manual-base.dvi.gz \
        Reference-Manual-addendum.ps.gz Reference-Manual-addendum.dvi.gz\
        Reference-Manual-all.ps.gz Reference-Manual-all.dvi.gz\
        Library.dvi.gz Library.ps.gz\
        Tutorial.dvi.gz Tutorial.ps.gz\
        README all-ps-docs.tar.gz

FTPHTMLDOCS=doc-html.tar.gz

#########################
# Principal targets 
########################

all: check-env all-dvi all-pdf

check-env:
	if $(TEST) "$(COQBIN)" = ""; then echo "COQBIN undefined"; exit 1; fi
	if $(TEST) "$(COQTOP)" = ""; then echo "COQTOP undefined"; exit 1; fi

coq-part: $(REFMANCOQTEXFILES) $(COQTEXFILES) demos-programs library/libdoc.tex

latex-part: all-dvi

all-dvi: Tutorial.v.dvi Reference-Manual.dvi Library.dvi Changes.v.dvi

all-pdf: Tutorial.v.pdf Reference-Manual.pdf Library.pdf Changes.v.pdf

all-ps: Tutorial.v.ps Reference-Manual.ps Library.ps Changes.v.ps

all-html: Tutorial.v.html Reference-Manual.html Library.html Changes.v.html


# dvips et dviselect existent sur loupiac
distrib:
	make clean-coq demos-programs
	make clean-latex all-dvi all-ps all-pdf compress-latex
	make clean-html all-html doc-html.tar.gz html-www

compress-latex:
	sh Reference-Manual.sh
	mv -f Reference-Manual.ps Reference-Manual-all.ps
	mv -f Tutorial.v.ps Tutorial.ps
	mv -f Tutorial.v.dvi Tutorial.dvi
	mv -f Reference-Manual.dvi Reference-Manual-all.dvi
	mv -f Changes.v.ps Changes.ps
	mv -f Changes.v.dvi Changes.dvi
	- mv -f Tutorial.v.pdf Tutorial.pdf
	- mv -f Changes.v.pdf Changes.pdf
	tar cf all-ps-docs.tar Reference-Manual-base.ps \
	  Reference-Manual-addendum.ps Changes.ps Tutorial.ps Library.ps
	gzip *.ps
	gzip *.dvi
	gzip *.pdf
	gzip all-ps-docs.tar

Tutorial.v.html: Tutorial.v.tex
	hevea ./book-html.sty ./coq-html.sty ./Tutorial.v.tex

Changes.v.html: Changes.v.tex
	hevea ./Changes.v.tex

Reference-Manual.html: 
	hevea ./book-html.sty ./coq-html.sty ./Reference-Manual.tex

doc-html.tar.gz: all-html
	- $(MKDIR) coq-docs-html
	rm -rf coq-docs-html/*
	cp Tutorial.v.html coq-docs-html/tutorial.html
	cp Changes.v.html coq-docs-html/changes.html
	cp Reference-Manual.html coq-docs-html 
	(cd coq-docs-html;\
	 htmlsplit -N -T "The Coq Proof Assistant Reference Manual"\
	   ./Reference-Manual.html; rm ./Reference-Manual.html)
	cp cover.html coq-docs-html
	tar cf doc-html.tar coq-docs-html
	gzip doc-html.tar

# Pour le site de Coq.
html-www: all-html
	- $(MKDIR) www
	rm -rf www/*
	cp Tutorial.v.html www/tutorial.html
	cp Changes.v.html www/changes.html
	cp Reference-Manual.html www
	(cd www;\
	 htmlsplit -N -T "The Coq Proof Assistant Reference Manual"\
	   -n ../icons/next.gif -p ../icons/prev.gif -r ../icons/root.gif\
	   -s ../icons/sub.gif ./Reference-Manual.html;\
	 rm ./Reference-Manual.html)
	cp cover.html www


clean-refman:
	rm -f Reference-Manual.toc Reference-Manual.idx Reference-Manual.atoc\
	  Reference-Manual.aux Reference-Manual.bbl Reference-Manual.blg\
	  Reference-Manual.ilg Reference-Manual.ind\
	  Reference-Manual.tacidx Reference-Manual.tacind\
	  Reference-Manual.comidx Reference-Manual.comind\
	  Reference-Manual.erridx Reference-Manual.errind\
          Reference-Manual.dvi Reference-Manual.ps\
	  Reference-Manual.sh\
	  $(REFMANFILES:.tex=.aux) $(REFMANFILES:.tex=.log)\
	  $(COQTEXFILES:.tex=.aux) $(COQTEXFILES:.tex=.log)

clean-latex: clean-refman
	rm -f *.dvi *.aux *.log *.bbl *.blg *.ps *.toc *.idx *~ *.ilg *.ind\
	*.dvi.gz *.ps.gz *.pdf *.pdf.gz

clean-coq:
	rm -f *.v.tex avl.ml heapsort.ml euclid.ml library/libdoc.tex *.cm[io]

clean: clean-coq clean-latex

clean-html:
	rm -f Tutorial.v.html Changes.v.html Reference-Manual.html

cleanall: clean clean-html

#########################
# Implicit rules
#########################

.SUFFIXES: .dvi .tex .v.tex .ps .pdf

.tex.dvi:
	$(LATEX) $<
	$(LATEX) $<

.tex.pdf:
	$(PDFLATEX) $<
	$(PDFLATEX) $<

.tex.v.tex:
	$(COQTEX) $<

.dvi.ps:
	dvips -o $@ $<


##########################
# Dependencies
##########################

Library.dvi: $(INPUTS) library.coqweb.tex Library.tex
	$(LATEX) Library
	$(LATEX) Library

Library.pdf: $(INPUTS) library.coqweb.tex Library.tex
	$(PDFLATEX) Library
	$(PDFLATEX) Library

# The option -exec xxdate.exe is to product today's date (\today TeX macro)
Library.html: $(INPUTS) library.coqweb.tex Library.tex
	hevea ./coq-html.sty -exec xxdate.exe $(COQWEBSTY)/coqweb.sty ./Library.tex

LIBDIRS= Logic Bool Arith ZArith Reals Lists Sets Relations \
         Wellfounded IntMap

library.coqweb.tex: library.files
	WHERE=`pwd` ; \
	cd $(COQTOP)/theories; \
	coqweb --noweb -o $$WHERE/$@ --no-preamble `cat $$WHERE/library.files`

GALLINA=$(COQBIN)/gallina

# ls -tr trie les fichiers dans l'ordre inverse de leur date de création
# En supposant que make fait son boulot, ca fait un tri topologique du
# graphe des dépendances
library.files::
	rm -f library.files; touch library.files
	ABSOLUTE=`pwd`/library.files ; \
	for rep in $(LIBDIRS) ; do \
	  (cd $(COQTOP)/theories/$$rep ; \
	   echo $$rep/intro.tex >> $$ABSOLUTE ; \
	   VOFILES=`ls -tr *.vo` ; \
	   for file in $$VOFILES ; do \
		VF=`basename $$file \.vo` ; \
		if $(TEST) \( ! -e $$VF.g \) -o \( $$VF.v -nt $$VF.g \) ; then \
	          $(GALLINA) $$VF.v; fi ; \
		echo $$rep/$$VF.g >> $$ABSOLUTE ; \
           done \
	  ) ; \
	done

demos-programs:
#	(cd ../theories/DEMOS/PROGRAMS ; make all)

Recursive-Definition.v.tex: ./title.tex Recursive-Definition.tex

Tutorial.v.dvi: ./title.tex Tutorial.v.tex
Tutorial.v.pdf: ./title.tex Tutorial.v.tex

# RefMan-ppr.v.tex: ../tactics/eqdecide.cmo

# RefMan-tus.v.tex: ../tactics/EqDecide.vo ../tactics/eqdecide.cmo

Reference-Manual.ps: Reference-Manual.dvi

Reference-Manual.dvi: $(INPUTS) $(REFMANFILES) $(COQTEXFILES) biblio.bib
	rm -f Reference-Manual.sh
	$(LATEX) Reference-Manual
	rm Reference-Manual.sh
	$(BIBTEX) Reference-Manual
	$(LATEX) Reference-Manual
	rm Reference-Manual.sh
	$(BIBTEX) Reference-Manual
	$(LATEX) Reference-Manual
	rm Reference-Manual.sh
	$(MAKEINDEX) Reference-Manual
	$(MAKEINDEX) Reference-Manual.tacidx -o Reference-Manual.tacind
	$(MAKEINDEX) Reference-Manual.comidx -o Reference-Manual.comind
	$(MAKEINDEX) Reference-Manual.erridx -o Reference-Manual.errind
	$(LATEX) Reference-Manual
	rm Reference-Manual.sh
	$(LATEX) Reference-Manual

Reference-Manual.pdf: Reference-Manual.dvi
	rm -f Reference-Manual.sh
	$(PDFLATEX) Reference-Manual.tex

quick: $(INPUTS) $(REFMANFILES) $(COQTEXFILES) biblio.bib
	rm -f Reference-Manual.sh
	$(LATEX) Reference-Manual


###################
# RT
###################
# Fabrication d'un RT INRIA (utilise rrkit de Michel Mauny)
Reference-Manual-RT.dvi: Reference-Manual.dvi RefMan-cover.tex
	dviselect -i Reference-Manual.dvi -o RefMan-body.dvi 3:
	$(LATEX) RefMan-cover.tex
	set a=`tail -1 Reference-Manual.log`;\
	set a=expr \("$$a" : '.*(\(.*\) pages.*'\) % 2;\
	if $(TEST) "$$a = 0";\
	 then rrkit  RefMan-cover.dvi RefMan-body.dvi Reference-Manual-RT.dvi;\
	 else rrkit -odd RefMan-cover.dvi RefMan-body.dvi Reference-Manual-RT.dvi;\
	fi

# Fabrication d'un RT INRIA (utilise rrkit de Michel Mauny)
Tutorial-RT.dvi : Tutorial.v.dvi Tutorial-cover.tex
	dviselect -i Tutorial.v.dvi -o Tutorial-body.dvi 3:
	$(LATEX) Tutorial-cover.tex
	set a=`tail -1 Tutorial.v.log`;\
	set a=expr \("$$a" : '.*(\(.*\) pages.*'\) % 2;\
	if $(TEST) "$$a = 0";\
	 then rrkit      Tutorial-cover.dvi Tutorial-body.dvi Tutorial-RT.dvi;\
	 else rrkit -odd Tutorial-cover.dvi Tutorial-body.dvi Tutorial-RT.dvi;\
	fi

################ doc ftp and www installation ############
doc-ftp-www-install: doc-ftp-install doc-www-install

doc-ftp-install: 
	- mkdir $(FTPDOCDIR)
	cp $(ALLFTPDOCS) $(FTPHTMLDOCS) $(FTPDOCDIR)
	chmod g+w $(FTPDOCDIR)/*

doc-www-install: 
	(cd $(WWWDOCDIR); rm -f node*.html main*.html toc.html \
	 tutorial.html changes.html cover.html)
	cp www/* $(WWWDOCDIR)
