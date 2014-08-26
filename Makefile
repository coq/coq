#######################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team    #
# <O___,, #        INRIA-Rocquencourt  &  LRI-CNRS-osay              #
#   \VV/  #############################################################
#    //   #      This file is distributed under the terms of the      #
#         #       GNU Lesser General Public License Version 2.1       #
#######################################################################


# Makefile for Coq
#
# To be used with GNU Make >= 3.81.
#
# This Makefile is now separated into Makefile.{common,build,doc}.
# You won't find Makefiles in sub-directories and this is done on purpose.
# If you are not yet convinced of the advantages of a single Makefile, please
# read
#    http://miller.emu.id.au/pmiller/books/rmch/
# before complaining.
# 
# When you are working in a subdir, you can compile without moving to the
# upper directory using "make -C ..", and the output is still understood
# by Emacs' next-error.
#
# Specific command-line options to this Makefile:
#
# make VERBOSE=1           # restore the raw echoing of commands
# make NO_RECALC_DEPS=1    # avoid recomputing dependencies
#
# Nota: the 1 above can be replaced by any non-empty value
#
# ----------------------------------------------------------------------
# See dev/doc/build-system*.txt for more details/FAQ about this Makefile
# ----------------------------------------------------------------------


###########################################################################
# File lists
###########################################################################

# NB: due to limitations in Win32, please refrain using 'export' too much
# to communicate between make sub-calls (in Win32, 8kb max per env variable,
# 32kb total)

# !! Before using FIND_VCS_CLAUSE, please read how you should in the !!
# !! FIND_VCS_CLAUSE section of dev/doc/build-system.dev.txt         !!
FIND_VCS_CLAUSE:='(' \
  -name '{arch}' -o \
  -name '.svn' -o \
  -name '_darcs' -o \
  -name '.git' -o \
  -name '.bzr' -o \
  -name 'debian' -o \
  -name "$${GIT_DIR}" -o \
  -name '_build' \
')' -prune -o

define find
 $(shell find . $(FIND_VCS_CLAUSE) '(' -name $(1) ')' -print | sed 's|^\./||')
endef

define findx
 $(shell find . $(FIND_VCS_CLAUSE) '(' -name $(1) ')' -exec $(2) {} \; | sed 's|^\./||')
endef

# We now discriminate .ml4 files according to their need of grammar.cma
# or q_constr.cmo
USEGRAMMAR := '(\*.*camlp4deps.*grammar'

## Files in the source tree

YACCFILES:=$(call find, '*.mly')
LEXFILES := $(call find, '*.mll')
export MLLIBFILES := $(call find, '*.mllib')
export ML4BASEFILES := $(call findx, '*.ml4', grep -L -e $(USEGRAMMAR))
export ML4FILES := $(call find, '*.ml4')
export CFILES := $(call find, '*.c')

# NB: The lists of currently existing .ml and .mli files will change
# before and after a build or a make clean. Hence we do not export
# these variables, but cleaned-up versions (see below MLFILES and co)

EXISTINGML := $(call find, '*.ml')
EXISTINGMLI := $(call find, '*.mli')

## Files that will be generated

GENML4FILES:= $(ML4FILES:.ml4=.ml)
GENMLIFILES:=$(YACCFILES:.mly=.mli)
GENPLUGINSMOD:=$(filter plugins/%,$(MLLIBFILES:%.mllib=%_mod.ml))
export GENMLFILES:=$(LEXFILES:.mll=.ml) $(YACCFILES:.mly=.ml) \
  tools/tolink.ml kernel/copcodes.ml $(GENPLUGINSMOD)
export GENHFILES:=kernel/byterun/coq_jumptbl.h
export GENVFILES:=theories/Numbers/Natural/BigN/NMake_gen.v
export GENFILES:=$(GENMLFILES) $(GENMLIFILES) $(GENHFILES) $(GENVFILES)

# NB: all files in $(GENFILES) can be created initially, while
# .ml files in $(GENML4FILES) might need some intermediate building.
# That's why we keep $(GENML4FILES) out of $(GENFILES)

## More complex file lists

define diff
 $(strip $(foreach f, $(1), $(if $(filter $(f),$(2)),,$f)))
endef

export MLSTATICFILES := $(call diff, $(EXISTINGML), $(GENMLFILES) $(GENML4FILES))
export MLIFILES := $(sort $(GENMLIFILES) $(EXISTINGMLI))

include Makefile.common

###########################################################################
# Starting rules
###########################################################################

NOARG: world

.PHONY: NOARG help noconfig submake

help:
	@echo "Please use either"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make clean"
	@echo "or make archclean"
	@echo
	@echo "For make to be verbose, add VERBOSE=1"

UNSAVED_FILES:=$(shell find . -name '.\#*v' -o -name '.\#*.ml' -o -name '.\#*.ml?')
ifdef UNSAVED_FILES
$(error You have unsaved changes in your editor (emacs?) [$(UNSAVED_FILES)]; \
cancel them or save before proceeding. Or your editor crashed. \
Then, you may want to consider whether you want to restore the autosaves)
#If you try to simply remove this explicit test, the compilation may
#fail later. In particular, if a .#*.v file exists, coqdep fails to
#run.
endif

# Apart from clean and tags, everything will be done in a sub-call to make
# on Makefile.build. This way, we avoid doing here the -include of .d :
# since they trigger some compilations, we do not want them for a mere clean.
# Moreover, we regroup this sub-call in a common target named 'submake'.
# This way, multiple user-given goals (cf the MAKECMDGOALS variable) won't
# trigger multiple (possibly parallel) make sub-calls

ifdef COQ_CONFIGURED
%:: submake ;
else
%:: noconfig ;
endif

MAKE_OPTS := --warn-undefined-variable --no-builtin-rules

GRAM_TARGETS := grammar/grammar.cma grammar/q_constr.cmo

submake:
	$(MAKE) $(MAKE_OPTS) -f Makefile.build BUILDGRAMMAR=1 $(GRAM_TARGETS)
	$(MAKE) $(MAKE_OPTS) -f Makefile.build $(MAKECMDGOALS)

noconfig:
	@echo "Please run ./configure first" >&2; exit 1

# To speed-up things a bit, let's dissuade make to attempt rebuilding makefiles

Makefile Makefile.build Makefile.common config/Makefile : ;

###########################################################################
# Cleaning
###########################################################################

.PHONY: clean cleankeepvo objclean cruftclean indepclean doclean archclean optclean clean-ide ml4clean ml4depclean depclean cleanconfig distclean voclean devdocclean

clean: objclean cruftclean depclean docclean devdocclean

cleankeepvo: indepclean clean-ide optclean cruftclean depclean docclean devdocclean

objclean: archclean indepclean

cruftclean: ml4clean
	find . -name '*~' -o -name '*.annot' | xargs rm -f
	rm -f gmon.out core

indepclean:
	rm -f $(GENFILES)
	rm -f $(COQTOPBYTE) $(CHICKENBYTE) $(FAKEIDE)
	find . \( -name '*~' -o -name '*.cm[ioat]' -o -name '*.cmti' \) -delete
	rm -f */*.pp[iox] plugins/*/*.pp[iox]
	rm -rf $(SOURCEDOCDIR)
	rm -f toplevel/mltop.byteml toplevel/mltop.optml
	rm -f test-suite/check.log
	rm -f glob.dump
	rm -f config/revision.ml revision
	$(MAKE) -C test-suite clean

docclean:
	rm -f doc/*/*.dvi doc/*/*.aux doc/*/*.log doc/*/*.bbl doc/*/*.blg doc/*/*.toc \
	doc/*/*.idx doc/*/*~ doc/*/*.ilg doc/*/*.ind doc/*/*.dvi.gz doc/*/*.ps.gz doc/*/*.pdf.gz\
	doc/*/*.???idx doc/*/*.???ind doc/*/*.v.tex doc/*/*.atoc doc/*/*.lof\
	doc/*/*.hatoc doc/*/*.haux doc/*/*.hcomind doc/*/*.herrind doc/*/*.hidx doc/*/*.hind \
	doc/*/*.htacind doc/*/*.htoc doc/*/*.v.html
	rm -f doc/stdlib/index-list.html doc/stdlib/index-body.html \
	  doc/stdlib/*Library.coqdoc.tex doc/stdlib/library.files \
	  doc/stdlib/library.files.ls doc/stdlib/FullLibrary.tex
	rm -f doc/*/*.ps doc/*/*.pdf
	rm -rf doc/refman/html doc/stdlib/html doc/faq/html doc/tutorial/tutorial.v.html
	rm -f doc/refman/euclid.ml doc/refman/euclid.mli
	rm -f doc/refman/heapsort.ml doc/refman/heapsort.mli
	rm -f doc/common/version.tex
	rm -f doc/refman/styles.hva doc/refman/cover.html doc/refman/Reference-Manual.html
	rm -f doc/coq.tex

archclean: clean-ide optclean voclean
	rm -rf _build
	rm -f $(ALLSTDLIB).*

optclean:
	rm -f $(COQTOPEXE) $(COQMKTOP) $(COQC) $(CHICKEN) $(COQDEPBOOT)
	rm -f $(TOOLS) $(CSDPCERT)
	find . -name '*.cmx' -o -name '*.cmxs' -o -name '*.cmxa' -o -name '*.[soa]' -o -name '*.so' | xargs rm -f

clean-ide:
	rm -f $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDE)
	rm -f ide/input_method_lexer.ml
	rm -f ide/highlight.ml ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml
	rm -rf $(COQIDEAPP)

ml4clean:
	rm -f $(GENML4FILES)

ml4depclean:
	find . -name '*.ml4.d' | xargs rm -f

depclean:
	find . $(FIND_VCS_CLAUSE) '(' -name '*.d' ')' -print | xargs rm -f

cacheclean:
	find theories plugins test-suite -name '.*.aux' -delete

cleanconfig:
	rm -f config/Makefile config/coq_config.ml myocamlbuild_config.ml dev/ocamldebug-v7 config/Info-*.plist

distclean: clean cleanconfig cacheclean

voclean:
	find theories plugins test-suite \( -name '*.vo' -o -name '*.glob' -o -name "*.cmxs" -o -name "*.native" -o -name "*.cmx" -o -name "*.cmi" -o -name "*.o" \) -delete

devdocclean:
	find . -name '*.dep.ps' -o -name '*.dot' | xargs rm -f
	rm -f $(OCAMLDOCDIR)/*.log $(OCAMLDOCDIR)/*.aux $(OCAMLDOCDIR)/*.toc 
	rm -f $(OCAMLDOCDIR)/ocamldoc.sty $(OCAMLDOCDIR)/coq.tex 
	rm -f $(OCAMLDOCDIR)/html/*.html

###########################################################################
# Emacs tags
###########################################################################

.PHONY: tags printenv

tags:
	echo $(filter-out checker/%, $(MLIFILES)) $(filter-out checker/%, $(MLSTATICFILES)) $(ML4FILES) | sort -r | xargs \
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

checker-tags:
	echo $(filter-out kernel/%, $(MLIFILES)) $(filter-out kernel/%, $(MLSTATICFILES)) $(ML4FILES) | sort -r | xargs \
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

# Useful to check that the exported variables are within the win32 limits

printenv:
	@env
	@echo
	@echo -n "Maxsize (win32 limit is 8k) : "
	@env | wc -L
	@echo -n "Total (win32 limit is 32k) : "
	@env | wc -m

