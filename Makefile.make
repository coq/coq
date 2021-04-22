##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
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
# "-not -name ." to avoid skipping everything since we "find ."
# "-type d" to be able to find .merlin.in files
FIND_SKIP_DIRS:=-not -name . '(' \
  -name '.*' -type d -o \
  -name 'debian' -o \
  -name "$${GIT_DIR}" -o \
  -name '_build' -o \
  -name '_build_ci' -o \
  -name '_build_boot' -o \
  -name '_install_ci' -o \
  -name 'gramlib' -o \
  -name 'user-contrib' -o \
  -name 'test-suite' -o \
  -name 'plugin_tutorial' \
')' -prune -o

define find
 $(shell find . user-contrib/Ltac2 $(FIND_SKIP_DIRS) '(' -name $(1) ')' -print | sed 's|^\./||')
endef

define findindir
 $(shell find $(1) $(FIND_SKIP_DIRS) '(' -name $(2) ')' -print | sed 's|^\./||')
endef

###########################################################################
# Starting rules
###########################################################################

.PHONY: NOARG help noconfig submake

.DEFAULT_GOAL:=NOARG

NOARG: world byte

include Makefile.common

help:
	@echo "Please use either:"
	@echo "   ./configure"
	@echo "   make world"
	@echo "   make install"
	@echo "   make clean"
	@echo "or make archclean"
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

submake:
	$(MAKE) $(MAKE_OPTS) -f Makefile.build $(MAKECMDGOALS)

noconfig:
	@echo "Please run ./configure first" >&2; exit 1

# To speed-up things a bit, let's dissuade make to attempt rebuilding makefiles

Makefile $(wildcard Makefile.*) config/Makefile : ;

###########################################################################
# Cleaning
###########################################################################

.PHONY: clean cleankeepvo archclean depclean cleanconfig distclean voclean timingclean

clean: depclean voclean
	dune clean

cleankeepvo: depclean
	dune clean

archclean: voclean plugin-tutorialclean
	rm -rf _build _build_boot

depclean:
	find . $(FIND_SKIP_DIRS) '(' -name '*.d' ')' -exec rm -f {} +

OUT_DIRS=$(wildcard $(VO_OUT_DIR))

cacheclean:
	find $(OUT_DIRS) test-suite -name '.*.aux' -exec rm -f {} +

cleanconfig:
	rm -f config/Makefile config/coq_config.ml dev/ocamldebug-coq

distclean: clean cleanconfig cacheclean timingclean

voclean:
	find $(OUT_DIRS) test-suite  \( -name '*.vo' -o -name '*.vio' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) -exec rm -f {} +
	find $(OUT_DIRS) test-suite -name .coq-native -empty -exec rm -rf {} +

timingclean:
	find $(OUT_DIRS) test-suite \( -name '*.v.timing' -o -name '*.v.before-timing' \
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

###########################################################################
# Continuous Integration Tests
###########################################################################
include Makefile.ci
