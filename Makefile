#######################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team    #
# <O___,, #        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              #
#   \VV/  #############################################################
#    //   #      This file is distributed under the terms of the      #
#         #       GNU Lesser General Public License Version 2.1       #
#######################################################################

# $Id: Makefile,v 1.3# Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
# ast-based camlp4

parsing/lexer.cmx: parsing/lexer.ml4
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<

parsing/lexer.cmo: parsing/lexer.ml4
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` pr_o.cmo -impl" -c -impl $<



###########################################################################
# Default rules
###########################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .ml4 .v .vo .el .elc

.ml.cmo:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(BYTEFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -c $<

.mll.ml:
	ocamllex $<

.ml4.cmx:
	$(OCAMLOPT) $(OPTFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.ml4.cmo:
	$(OCAMLC) $(BYTEFLAGS) -pp "$(CAMLP4O) $(CAMLP4EXTENDFLAGS) `$(CAMLP4DEPS) $<` -impl" -c -impl $<

.v.vo:
	$(BOOTCOQTOP) -compile $*

.el.elc:
	echo "(setq load-path (cons \".\" load-path))" > $*.compile
	echo "(byte-compile-file \"$<\")" >> $*.compile
	- $(EMACS) -batch -l $*.compile
	rm -f $*.compile        

###########################################################################
# Cleaning
###########################################################################

archclean::
	rm -f config/*.cmx config/*.[so]
	rm -f lib/*.cmx lib/*.[so]
	rm -f kernel/*.cmx kernel/*.[so]
	rm -f library/*.cmx library/*.[so]
	rm -f proofs/*.cmx proofs/*.[so]
	rm -f tactics/*.cmx tactics/*.[so]
	rm -f interp/*.cmx interp/*.[so]
	rm -f parsing/*.cmx parsing/*.[so]
	rm -f pretyping/*.cmx pretyping/*.[so]
	rm -f toplevel/*.cmx toplevel/*.[so]
	rm -f ide/*.cmx ide/*.[so]
	rm -f tools/*.cmx tools/*.[so]
	rm -f scripts/*.cmx scripts/*.[so]
	rm -f dev/*.cmx dev/*.[so]

clean:: archclean
	rm -f *~ */*~ */*/*~
	rm -f gmon.out core
	rm -f config/*.cm[io]
	rm -f lib/*.cm[io]
	rm -f kernel/*.cm[io]
	rm -f library/*.cm[io]
	rm -f proofs/*.cm[io]
	rm -f tactics/*.cm[io]
	rm -f interp/*.cm[io]
	rm -f parsing/*.cm[io] parsing/*.ppo
	rm -f pretyping/*.cm[io]
	rm -f toplevel/*.cm[io]
	rm -f ide/*.cm[io]
	rm -f tools/*.cm[io]
	rm -f scripts/*.cm[io]
	rm -f dev/*.cm[io]
	rm -f */*.pp[iox] contrib/*/*.pp[iox]

cleanconfig::
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7

###########################################################################
# Dependencies
###########################################################################

alldepend: depend dependcoq 

dependcoq:: beforedepend
	$(COQDEP) -R theories Coq -R contrib Coq $(COQINCLUDES) $(ALLREALS:.vo=.v) $(ALLVO:.vo=.v) > .depend.coq

# Build dependencies ignoring failures in building ml files from ml4 files
# This is useful to rebuild dependencies when they are strongly corrupted:
# by making scratchdependml, one gets dependencies OK for .ml files and
# .ml4 files not using fancy parsers. This is sufficient to get beforedepend
# and depend targets successfully built
scratchdepend:: dependp4
	-$(MAKE) -k -f Makefile.dep $(ML4FILESML)
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
	$(MAKE) depend


# Computing the dependencies in camlp4 files is tricky.
# We proceed in several steps:

ML4FILESML = $(ML4FILES:.ml4=.ml)

# Expresses dependencies of the .ml4 files w.r.t their grammars
dependp4::
	rm -f .depend.camlp4
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".ml: " >> .depend.camlp4; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend.camlp4; \
	done

# Produce the .ml files using Makefile.dep
ml4filesml:: .depend.camlp4
	$(MAKE) -f Makefile.dep $(ML4FILESML)

depend: beforedepend dependp4 ml4filesml
# 1. We express dependencies of the .ml files w.r.t their grammars
# 2. Then we are able to produce the .ml files using Makefile.dep
# 3. We compute the dependencies inside the .ml files using ocamldep
	$(OCAMLDEP) $(DEPFLAGS) */*.mli */*/*.mli */*.ml */*/*.ml > .depend
# 4. We express dependencies of .cmo and .cmx files w.r.t their grammars
	for f in $(ML4FILES); do \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".cmo: " >> .depend; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend; \
	  printf "%s" `dirname $$f`/`basename $$f .ml4`".cmx: " >> .depend; \
	  echo `$(CAMLP4DEPS) $$f` >> .depend; \
	done
# 5. Finally, we erase the generated .ml files
	rm -f $(ML4FILESML)
# 6. Since .depend contains correct dependencies .depend.devel can be deleted
# (see dev/Makefile.dir for details about this file)
	if [ -e makefile ]; then >.depend.devel; else rm -f .depend.devel; fi

ml4clean::
	rm -f $(ML4FILESML)

clean::
	rm -f $(ML4FILESML)

include .depend
include .depend.coq


# this sets up developper supporting stuff
devel:	
	touch .depend.devel
	$(MAKE) -f dev/Makefile.devel setup-devel
	$(MAKE) dev/top_printers.cmo
