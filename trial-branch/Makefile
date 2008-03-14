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

FIND_VCS_CLAUSE:='(' -name '{arch}' -or -name '.svn' -or -name '_darcs' -or -name '.git' -or -name "$${GIT_DIR}" ')' -prune -or
FIND_PRINTF_P:=-print | sed 's|^\./||'

export YACCFILES:=$(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.mly' ')' $(FIND_PRINTF_P))
export LEXFILES := $(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.mll' ')' $(FIND_PRINTF_P))
export GENMLFILES:=$(LEXFILES:.mll=.ml) $(YACCFILES:.mly=.ml) \
  scripts/tolink.ml kernel/copcodes.ml
export GENMLIFILES:=$(YACCFILES:.mly=.mli)
export GENHFILES:=kernel/byterun/coq_jumptbl.h
export GENFILES:=$(GENMLFILES) $(GENMLIFILES) $(GENHFILES)
export MLFILES  := $(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.ml'  ')' $(FIND_PRINTF_P) | \
  while read f; do if ! [ -e "$${f}4" ]; then echo "$$f"; fi; done) \
  $(GENMLFILES)
export MLIFILES := $(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.mli' ')' $(FIND_PRINTF_P)) \
  $(GENMLIFILES)
export ML4FILES := $(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.ml4' ')' $(FIND_PRINTF_P))
export VFILES   := $(shell find . $(FIND_VCS_CLAUSE) '(' -name '*.v'   ')' $(FIND_PRINTF_P))
export CFILES   := $(shell find kernel/byterun -name '*.c')

export ML4FILESML:= $(ML4FILES:.ml4=.ml)

include Makefile.common

NOARG: world

.PHONY: NOARG help always tags otags

always: ;

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

ifdef GOTO_STAGE
config/Makefile Makefile.common Makefile.build Makefile: ;

%: always
	$(call stage-template,$(GOTO_STAGE))
else

.PHONY: stage1 stage2 stage3 world revision

# This is to remove the built-in rule "%: %.o"
# Otherwise, "make foo" recurses into stage1, trying to build foo.o .
%: %.o

%.o: always
	$(call stage-template,1)

#STAGE1_TARGETS includes all object files necessary for $(STAGE1)
stage1 $(STAGE1_TARGETS): always
	$(call stage-template,1)

CAML_OBJECT_PATTERNS:=%.cmo %.cmx %.cmi %.cma %.cmxa
ifdef CM_STAGE1
$(CAML_OBJECT_PATTERNS): always
	$(call stage-template,1)

%.ml4.preprocessed: stage1
	$(call stage-template,2)
else
$(CAML_OBJECT_PATTERNS) %.ml4.preprocessed: stage1
	$(call stage-template,2)
endif

stage2 $(STAGE2_TARGETS): stage1
	$(call stage-template,2)

%.vo %.glob states/% install-%: stage2
	$(call stage-template,3)

stage3 $(STAGE3_TARGETS): stage2
	$(call stage-template,3)

endif #GOTO_STAGE

###########################################################################
# Cleaning
###########################################################################

.PHONY: clean objclean cruftclean indepclean archclean ml4clean clean-ide ml4depclean depclean distclean cleanconfig cleantheories docclean

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
	rm -f $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDEOPT) $(COQIDE)
	rm -f ide/extract_index.ml ide/find_phrase.ml ide/highlight.ml
	rm -f ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml

ml4clean:
	rm -f $(ML4FILESML) $(ML4FILESML:.ml=.ml4.preprocessed)

ml4depclean:
	find . -name '*.ml4.d' | xargs rm -f

depclean:
	find . -name '*.d' | xargs rm -f

cleanconfig:
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-v7 ide/undo.mli

distclean: clean cleanconfig

cleantheories:
	rm -f states/*.coq
	find theories -name '*.vo' -or -name '*.glob' | xargs rm -f

###########################################################################
# Emacs tags
###########################################################################

tags:
	echo $(MLIFILES) $(MLFILES) $(ML4FILES) | sort -r | xargs \
	etags --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"
	echo $(ML4FILES) | sort -r | xargs \
	etags --append --language=none\
	      "--regex=/[ \t]*\([^: \t]+\)[ \t]*:/\1/"


otags: 
	echo $(MLIFILES) $(MLFILES) | sort -r | xargs otags
	echo $(ML4FILES) | sort -r | xargs \
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
