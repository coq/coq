##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################


# Makefile for Coq
#
# To be used with GNU Make >= 3.81.
#
# This Makefile is now separated into Makefile.{common,build,doc}.
# You won't find Makefiles in sub-directories and this is done on purpose.
# If you are not yet convinced of the advantages of a single Makefile, please
# read
#    http://aegis.sourceforge.net/auug97.pdf
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

# !! Before using FIND_SKIP_DIRS, please read how you should in the !!
# !! FIND_SKIP_DIRS section of dev/doc/build-system.dev.txt         !!
FIND_SKIP_DIRS:='(' \
  -name '{arch}' -o \
  -name '.svn' -o \
  -name '_darcs' -o \
  -name '.git' -o \
  -name '.bzr' -o \
  -name 'debian' -o \
  -name "$${GIT_DIR}" -o \
  -name '_build' -o \
  -name '_build_ci' -o \
  -name '_install_ci' -o \
  -name 'gramlib' -o \
  -name 'user-contrib' -o \
  -name 'test-suite' -o \
  -name '.opamcache' -o \
  -name '.coq-native' -o \
  -name 'plugin_tutorial' \
')' -prune -o

define find
 $(shell find . $(FIND_SKIP_DIRS) '(' -name $(1) ')' -print | sed 's|^\./||')
endef

define findindir
 $(shell find $(1) $(FIND_SKIP_DIRS) '(' -name $(2) ')' -print | sed 's|^\./||')
endef

## Files in the source tree

LEXFILES := $(call find, '*.mll')
YACCFILES := $(call find, '*.mly')
export MLLIBFILES := $(call find, '*.mllib')
export MLPACKFILES := $(call find, '*.mlpack')
export MLGFILES := $(call find, '*.mlg')
export CFILES := $(call findindir, 'kernel/byterun', '*.c')

# NB our find wrapper ignores the test suite
MERLININFILES := $(call find, '.merlin.in') test-suite/unit-tests/.merlin.in
export MERLINFILES := $(MERLININFILES:.in=)

# NB: The lists of currently existing .ml and .mli files will change
# before and after a build or a make clean. Hence we do not export
# these variables, but cleaned-up versions (see below MLFILES and co)

EXISTINGML := $(call find, '*.ml')
EXISTINGMLI := $(call find, '*.mli')

## Files that will be generated

GENMLGFILES:= $(MLGFILES:.mlg=.ml)
# GRAMFILES must be in linking order
export GRAMFILES=$(addprefix gramlib/.pack/gramlib__,Ploc Plexing Gramext Grammar)
export GRAMMLFILES := $(addsuffix .ml, $(GRAMFILES)) $(addsuffix .mli, $(GRAMFILES))
export GENGRAMFILES := $(GRAMMLFILES) gramlib/.pack/gramlib.ml
export GENMLFILES:=$(LEXFILES:.mll=.ml) $(YACCFILES:.mly=.ml) $(GENMLGFILES)  ide/coqide_os_specific.ml kernel/copcodes.ml kernel/uint63.ml
export GENHFILES:=kernel/byterun/coq_jumptbl.h
export GENFILES:=$(GENMLFILES) $(GENMLIFILES) $(GENHFILES)

## More complex file lists

export MLSTATICFILES := $(filter-out $(GENMLFILES), $(EXISTINGML))
export MLIFILES := $(sort $(GENMLIFILES) $(EXISTINGMLI))

include Makefile.common

###########################################################################
# Starting rules
###########################################################################

NOARG: world

.PHONY: NOARG help noconfig submake camldevfiles

help:
	@echo "Please use either:"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make clean"
	@echo "or make archclean"
	@echo "For make to be verbose, add VERBOSE=1"
	@echo
	@echo "Bytecode compilation is now a separate target:"
	@echo "   make byte"
	@echo "   make install-byte"
	@echo "Please do not mix bytecode and native targets in the same make -j"

UNSAVED_FILES:=$(shell find . -name '.\#*v' -o -name '.\#*.ml' -o -name '.\#*.ml?')
ifdef UNSAVED_FILES
$(error You have unsaved changes in your editor (emacs?) [$(UNSAVED_FILES)]; \
cancel them or save before proceeding. Or your editor crashed. \
Then, you may want to consider whether you want to restore the autosaves)
#If you try to simply remove this explicit test, the compilation may
#fail later. In particular, if a .#*.v file exists, coqdep fails to
#run.
endif

# Apart from clean and a few misc files, everything will be done in a
# sub-call to make on Makefile.build. This way, we avoid doing here
# the -include of .d : since they trigger some compilations, we do not
# want them for a mere clean. Moreover, we regroup this sub-call in a
# common target named 'submake'. This way, multiple user-given goals
# (cf the MAKECMDGOALS variable) won't trigger multiple (possibly
# parallel) make sub-calls

ifdef COQ_CONFIGURED
%:: submake ;
else
%:: noconfig ;
endif

MAKE_OPTS := --warn-undefined-variable --no-builtin-rules

bin:
	mkdir bin

submake: alienclean camldevfiles | bin
	$(MAKE) $(MAKE_OPTS) -f Makefile.build $(MAKECMDGOALS)

noconfig:
	@echo "Please run ./configure first" >&2; exit 1

# To speed-up things a bit, let's dissuade make to attempt rebuilding makefiles

Makefile $(wildcard Makefile.*) config/Makefile : ;

###########################################################################
# OCaml dev files
###########################################################################
camldevfiles: $(MERLINFILES) META.coq

# prevent submake dependency
META.coq.in $(MERLININFILES): ;

.merlin: .merlin.in
	cp -a "$<" "$@"

%/.merlin: %/.merlin.in
	cp -a "$<" "$@"

META.coq: META.coq.in
	cp -a "$<" "$@"

###########################################################################
# Cleaning
###########################################################################

.PHONY: clean cleankeepvo objclean cruftclean indepclean docclean archclean optclean plugin-tutorialclean clean-ide mlgclean depclean cleanconfig distclean voclean timingclean alienclean

clean: objclean cruftclean depclean docclean camldevfilesclean gramlibclean

cleankeepvo: indepclean clean-ide optclean cruftclean depclean docclean

objclean: archclean indepclean

.PHONY: gramlibclean
gramlibclean:
	rm -rf gramlib/.pack/

cruftclean: mlgclean
	find . \( -name '*~' -o -name '*.annot' \) -exec rm -f {} +
	rm -f gmon.out core

camldevfilesclean:
	rm -f $(MERLINFILES) META.coq

indepclean:
	rm -f $(GENFILES)
	rm -f $(COQTOPBYTE) $(CHICKENBYTE) $(TOPBYTE)
	find . \( -name '*~' -o -name '*.cm[ioat]' -o -name '*.cmti' \) -exec rm -f {} +
	rm -f */*.pp[iox] plugins/*/*.pp[iox]
	rm -rf $(SOURCEDOCDIR)
	rm -f toplevel/mltop.byteml toplevel/mltop.optml
	rm -f glob.dump
	rm -f config/revision.ml revision
	rm -f plugins/micromega/.micromega.ml.generated
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
	rm -f doc/*/*.ps doc/*/*.pdf doc/*/*.eps doc/*/*.pdf_t doc/*/*.eps_t
	rm -rf doc/stdlib/html doc/tutorial/tutorial.v.html
	rm -f doc/common/version.tex
	rm -f doc/coq.tex
	rm -rf doc/sphinx/_build

archclean: clean-ide optclean voclean plugin-tutorialclean
	rm -rf _build
	rm -f $(ALLSTDLIB).*

optclean:
	rm -f $(COQTOPEXE) $(CHICKEN) $(TOPBINOPT)
	rm -f $(TOOLS) $(PRIVATEBINARIES) $(CSDPCERT)
	find . \( -name '*.cmx' -o -name '*.cmx[as]' -o -name '*.[soa]' -o -name '*.so' \) -exec rm -f {} +

clean-ide:
	rm -f $(COQIDECMO) $(COQIDECMX) $(COQIDECMO:.cmo=.cmi) $(COQIDEBYTE) $(COQIDE)
	rm -f ide/input_method_lexer.ml
	rm -f ide/highlight.ml ide/config_lexer.ml ide/config_parser.mli ide/config_parser.ml
	rm -f ide/utf8_convert.ml
	rm -rf $(COQIDEAPP)

mlgclean:
	rm -f $(GENMLGFILES)

depclean:
	find . $(FIND_SKIP_DIRS) '(' -name '*.d' ')' -exec rm -f {} +

cacheclean:
	find theories plugins test-suite -name '.*.aux' -exec rm -f {} +

cleanconfig:
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-coq config/Info-*.plist

distclean: clean cleanconfig cacheclean timingclean

voclean:
	find theories plugins test-suite \( -name '*.vo' -o -name '*.vio' -o -name '*.glob' -o -name "*.cmxs" \
	-o -name "*.native" -o -name "*.cmx" -o -name "*.cmi" -o -name "*.o" \) -exec rm -f {} +
	find theories plugins test-suite -name .coq-native -empty -exec rm -rf {} +

timingclean:
	find theories plugins test-suite \( -name '*.v.timing' -o -name '*.v.before-timing' \
	  -o -name "*.v.after-timing" -o -name "*.v.timing.diff" -o -name "time-of-build.log" \
	  -o -name "time-of-build-before.log" -o -name "time-of-build-after.log" \
	  -o -name "time-of-build-pretty.log" -o -name "time-of-build-both.log" \) -exec rm -f {} +

plugin-tutorialclean:
	+$(MAKE) -C $(PLUGINTUTO) clean

# Ensure that every compiled file around has a known source file.
# This should help preventing weird compilation failures caused by leftover
# compiled files after deleting or moving some source files.

EXISTINGVO:=$(call find, '*.vo')
KNOWNVO:=$(patsubst %.v,%.vo,$(call find, '*.v'))
ALIENVO:=$(filter-out $(KNOWNVO),$(EXISTINGVO))

EXISTINGOBJS:=$(call find, '*.cm[oxia]' -o -name '*.cmxa')
KNOWNML:=$(EXISTINGML) $(GENMLFILES) $(MLPACKFILES:.mlpack=.ml) \
 $(patsubst %.mlp,%.ml,$(wildcard grammar/*.mlp))
KNOWNOBJS:=$(KNOWNML:.ml=.cmo) $(KNOWNML:.ml=.cmx) $(KNOWNML:.ml=.cmi) \
 $(MLIFILES:.mli=.cmi) \
 gramlib/.pack/gramlib.cma gramlib/.pack/gramlib.cmxa $(MLLIBFILES:.mllib=.cma) $(MLLIBFILES:.mllib=.cmxa) grammar/grammar.cma
ALIENOBJS:=$(filter-out $(KNOWNOBJS),$(EXISTINGOBJS))

alienclean:
	rm -f $(ALIENOBJS) $(ALIENVO)

###########################################################################
# Continuous Intregration Tests
###########################################################################
include Makefile.ci

###########################################################################
# Emacs tags
###########################################################################

.PHONY: tags printenv

tags:
	echo $(filter-out checker/%, $(MLIFILES)) $(filter-out checker/%, $(MLSTATICFILES)) $(MLGFILES) | sort -r | xargs \
	etags --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"
	echo $(MLGFILES) | sort -r | xargs \
	etags --append --language=none\
	      "--regex=/[ \t]*\([^: \t]+\)[ \t]*:/\1/"

checker-tags:
	echo $(filter-out kernel/%, $(MLIFILES)) $(filter-out kernel/%, $(MLSTATICFILES)) $(MLGFILES) | sort -r | xargs \
	etags --language=none\
	      "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"
	echo $(MLGFILES) | sort -r | xargs \
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
