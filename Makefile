#######################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team    #
# <O___,, #        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              #
#   \VV/  #############################################################
#    //   #      This file is distributed under the terms of the      #
#         #       GNU Lesser General Public License Version 2.1       #
#######################################################################

# $Id$ 


# Makefile for Coq
#
# To be used with GNU Make.
#
# This is the only Makefile. You won't find Makefiles in sub-directories
# and this is done on purpose. If you are not yet convinced of the advantages
# of a single Makefile, please read
#    http://www.pcug.org.au/~millerp/rmch/recu-make-cons-harm.html
# before complaining.
# 
# When you are working in a subdir, you can compile without moving to the
# upper directory using "make -C ..", and the output is still understood
# by Emacs' next-error.
###########################################################################

include Makefile.common

NOARG: world

.PHONY: stage1 stage2 stage3 NOARG help world revision always tags otags

always:

help:
	@echo "Please use either"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make clean"
	@echo "or make archclean"
	@echo
	@echo "For make to be verbose, add VERBOSE=1"

ifdef COQ_CONFIGURED
define stage-template
	@echo '*****************************************************'
	@echo '*****************************************************'
	@echo '****************** Entering stage$(1) ******************'
	@echo '*****************************************************'
	@echo '*****************************************************'
	+$(MAKE) -f Makefile.stage$(1) "$@"
endef
else
define stage-template
	@echo "Please run ./configure first" >&2; exit 1
endef
endif

UNSAVED_FILES:=$(shell find . -name '.\#*')
ifdef UNSAVED_FILES
$(error You have unsaved changes in your editor (emacs?); cancel them or save before proceeding. \
Or your editor crashed. Then, you may want to consider whether you want to restore the autosaves)
#If you try to simply remove this explicit test, the compilation may
#fail later. In particular, if a .#*.v file exists, coqdep fails to
#run.
endif

%.o: always
	$(call stage-template,1)

#STAGE1_TARGETS includes all object files necessary for $(STAGE1)
stage1 $(STAGE1_TARGETS): always
	$(call stage-template,1)

%.cmo %.cmx %.cmi %.cma %.cmxa %.ml4.preprocessed: stage1
	$(call stage-template,2)

stage2 $(STAGE2_TARGETS): stage1
	$(call stage-template,2)

%.vo %.glob states/% install-%: stage2
	$(call stage-template,3)

stage3 $(STAGE3_TARGETS): stage2
	$(call stage-template,3)

glob.dump: stage2
	$(call stage-template,3)

###########################################################################
# Cleaning
###########################################################################

.PHONY: clean objclean cruftclean indepclean archclean ml4clean clean-ide depclean distclean cleanconfig cleantheories docclean

clean: objclean cruftclean depclean docclean

objclean: archclean indepclean

cruftclean: ml4clean
	find . -name '*~' -or -name '*.annot' | xargs rm -f
	rm -f gmon.out core

indepclean:
	rm -f $(GENFILES)
	rm -f $(COQTOPBYTE) $(COQCBYTE) bin/coq-interface$(EXE) bin/parser$(EXE)
	find . -name '*~' -or -name '*.cm[ioa]' | xargs rm -f
	find contrib -name '*.vo' -or -name '*.glob' | xargs rm -f
	rm -f */*.pp[iox] contrib/*/*.pp[iox]
	rm -rf $(SOURCEDOCDIR)
	rm -f toplevel/mltop.byteml toplevel/mltop.optml
	rm -f glob.dump
	rm -f revision

docclean:
ifdef COQ_CONFIGURED
	$(MAKE) -C doc clean
else
	$(warning Clean of documentation requires "./configure" to be run; not done.)
endif

archclean: clean-ide cleantheories
	rm -f $(COQTOPOPT) $(BESTCOQTOP) $(COQC) $(COQMKTOP)
	rm -f $(COQTOP)  $(COQCOPT) $(COQMKTOPOPT)
	rm -f bin/parser.opt$(EXE) bin/coq-interface.opt$(EXE)
	find . -name '*.cmx' -or -name '*.cmxa' -or -name '*.[soa]' | xargs rm -f
	rm -f $(TOOLS)
	rm -f $(MINICOQ)

clean-ide:
	rm -f $(COQIDEVO) $(COQIDEVO:.vo=.glob) $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE)
	rm -f ide/extract_index.ml ide/find_phrase.ml ide/highlight.ml
	rm -f ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml

ml4clean:
	rm -f $(ML4FILESML) $(ML4FILESML:.ml=.ml4.preprocessed)

depclean:
	find . -name '*.d' | xargs  rm -f

cleanconfig:
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7 ide/undo.mli

distclean: clean cleanconfig

cleantheories:
	rm -f states/*.coq
	find theories -name '*.vo' -or -name '*.glob' | xargs rm -f

###########################################################################
# Emacs tags
###########################################################################

# NB: the -maxdepth 3 is for excluding files from contrib/extraction/test

tags:
	find . -maxdepth 3 -regex ".*\.ml[i4]?" | sort -r | xargs \
	etags --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"
	find . -maxdepth 3 -name "*.ml4" | sort -r | xargs \
	etags --append --language=none\
	      "--regex=/[ \t]*\([^: \t]+\)[ \t]*:/\1/"


otags: 
	find . -maxdepth 3 -name "*.ml" -o -name "*.mli" \
	| sort -r | xargs otags
	find . -maxdepth 3 -name "*.ml4" | sort -r | xargs \
	etags --append --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"


%.elc: %.el
ifdef COQ_CONFIGURED
	echo "(setq load-path (cons \".\" load-path))" > $*.compile
	echo "(byte-compile-file \"$<\")" >> $*.compile
	- $(EMACS) -batch -l $*.compile
	rm -f $*.compile
else
	@echo "Please run ./configure first" >&2; exit 1
endif

# This is to remove the built-in rule "%: %.o"
# Otherwise, "make foo" recurses into stage1, trying to build foo.o .
%: %.o
