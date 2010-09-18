#######################################################################
#  v      #   The Coq Proof Assistant  /  The Coq Development Team    #
# <O___,, #     INRIA-Rocquencourt  &  CNRS-Universite Paris Diderot  #
#   \VV/  #############################################################
#    //   #      This file is distributed under the terms of the      #
#         #       GNU Lesser General Public License Version 2.1       #
#######################################################################

# This is a standalone Makefile to run the test-suite. It can be used
# outside of the Coq source tree (if BIN is overridden).

# There is one %.v.log target per %.v test file. The target will be
# filled with the output, timings and status of the test. There is
# also one target per directory containing %.v files, that runs all
# the tests in it. As convenience, there is also the "bugs" target
# that runs all bug-related tests.

# The "summary" target outputs a summary of all tests that were run
# (but doesn't run them)

# The "run" target runs all tests that have not been run yet. To force
# all tests to be run, use the "clean" target.

#######################################################################
# Variables
#######################################################################

# Default value when called from a freshly compiled Coq, but can be
# easily overridden
BIN := ../bin/
LIB := ..

ifeq ($(BEST),byte)
  coqtop := $(BIN)coqtop.byte -boot -q -batch -I prerequisite
  bincoqc := $(BIN)coqc -coqlib $(LIB) -byte -I prerequisite
else
  coqtop := $(BIN)coqtop -boot -q -batch -I prerequisite
  bincoqc := $(BIN)coqc -coqlib $(LIB) -I prerequisite
endif

command := $(coqtop) -top Top -load-vernac-source
coqc := $(coqtop) -compile
coqdep := $(BIN)coqdep

SHOW := $(if $(VERBOSE),@true,@echo)
HIDE := $(if $(VERBOSE),,@)
REDIR := $(if $(VERBOSE),,> /dev/null 2>&1)

ifneq (,$(wildcard /proc/cpuinfo))
  sedbogo := -e "s/bogomips.*: \([0-9]*\).*/\1/p" # i386, ppc
  sedbogo += -e "s/Cpu0Bogo.*: \([0-9]*\).*/\1/p" # sparc
  sedbogo += -e "s/BogoMIPS.*: \([0-9]*\).*/\1/p" # alpha
  bogomips := $(shell sed -n $(sedbogo) /proc/cpuinfo | head -1)
endif

ifeq (,$(bogomips))
  $(warning cannot run complexity tests (no bogomips found))
endif

log_success = "==========> SUCCESS <=========="
log_failure = "==========> FAILURE <=========="
log_intro = "==========> TESTING $(1) <=========="

#######################################################################
# Testing subsystems
#######################################################################

# Apart so that it can be easily skipped with overriding
COMPLEXITY := $(if $(bogomips),complexity)

BUGS := bugs/opened/shouldnotfail bugs/opened/shouldnotsucceed \
  bugs/closed/shouldsucceed bugs/closed/shouldfail

VSUBSYSTEMS := prerequisite success failure $(BUGS) output \
  interactive micromega $(COMPLEXITY) modules

# All subsystems
SUBSYSTEMS := $(VSUBSYSTEMS) misc bugs

#######################################################################
# Phony targets
#######################################################################

.DELETE_ON_ERROR:
.PHONY: all run clean $(SUBSYSTEMS)

all: run
	$(MAKE) --quiet summary.log

run: $(SUBSYSTEMS)
bugs: $(BUGS)

clean:
	rm -f trace lia.cache
	$(SHOW) "RM        <**/*.stamp> <**/*.vo> <**/*.log>"
	$(HIDE)find . \( \
	  -name '*.stamp' -o -name '*.vo' -o -name '*.v.log' \
	\) -print0 | xargs -0 rm -f

distclean: clean
	$(HIDE)find . -name '*.log' -print0 | xargs -0 rm -f

#######################################################################
# Per-subsystem targets
#######################################################################

define mkstamp
$(1): $(1).stamp ; @true
$(1).stamp: $(patsubst %.v,%.v.log,$(wildcard $(1)/*.v)) ; \
	$(HIDE)touch $$@
endef
$(foreach S,$(VSUBSYSTEMS),$(eval $(call mkstamp,$(S))))

#######################################################################
# Summary
#######################################################################

summary_dir = echo $(1); find $(2) -name '*.log' -print0 | xargs -0 tail -q -n1 | sort -g

.PHONY: summary summary.log

summary:
	@{ \
	  $(call summary_dir, "Preparing tests", prerequisite); \
	  $(call summary_dir, "Success tests", success); \
	  $(call summary_dir, "Failure tests", failure); \
	  $(call summary_dir, "Bugs tests", bugs); \
	  $(call summary_dir, "Output tests", output); \
	  $(call summary_dir, "Interactive tests", interactive); \
	  $(call summary_dir, "Micromega tests", micromega); \
	  $(call summary_dir, "Miscellaneous tests", misc); \
	  $(call summary_dir, "Complexity tests", complexity); \
	  $(call summary_dir, "Module tests", modules); \
	  nb_success=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_success) | wc -l`; \
	  nb_failure=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_failure) | wc -l`; \
	  nb_tests=`expr $$nb_success + $$nb_failure`; \
	  pourcentage=`expr 100 \* $$nb_success / $$nb_tests`; \
	  echo; \
	  echo "$$nb_success tests passed over $$nb_tests, i.e. $$pourcentage %"; \
	}

summary.log:
	$(SHOW) SUMMARY
	$(HIDE)$(MAKE) --quiet summary > "$@"

#######################################################################
# Regression (and progression) tests
#######################################################################

# Process verifications concerning submitted bugs. A message is
# printed for all opened bugs (still active or seems to be closed).
# For closed bugs that behave as expected, no message is printed

# All files are assumed to have <# of the bug>.v as a name

# Opened bugs that should not succeed (FIXME: there were no such tests
# at the time of writing this Makefile, but the possibility was in the
# original shellscript... so left it here, but untested)
$(addsuffix .log,$(wildcard bugs/opened/shouldnotsucceed/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  $(call test_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...still active"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be closed, please check)";
	  fi;
	} > "$@"

# Opened bugs that should not fail
$(addsuffix .log,$(wildcard bugs/opened/shouldnotfail/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...still active"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be closed, please check)"; \
	  fi; \
	} > "$@"

# Closed bugs that should succeed
$(addsuffix .log,$(wildcard bugs/closed/shouldsucceed/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be opened, please check)"; \
	  fi; \
	} > "$@"

# Closed bugs that should fail
$(addsuffix .log,$(wildcard bugs/closed/shouldfail/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be opened, please check)"; \
	  fi; \
	} > "$@"

#######################################################################
# Other generic tests
#######################################################################

$(addsuffix .log,$(wildcard prerequisite/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqc) "$*" 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be prepared" ; \
	  else \
	    echo $(log_success); \
	    echo "    $<...correctly prepared" ; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard success/*.v micromega/*.v modules/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  opts="$(if $(findstring modules/,$<),-I modules -impredicative-set)"; \
	  echo $(call log_intro,$<); \
	  $(command) "$<" $$opts 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard failure/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be rejected)"; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard output/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  tmpoutput=`mktemp /tmp/coqcheck.XXXXXX`; \
	  $(command) "$<" 2>&1 \
	    | grep -v "Welcome to Coq" \
	    | grep -v "Skipping rcfile loading" \
	    > $$tmpoutput; \
	  diff $$tmpoutput $*.out 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	  fi; \
	  rm $$tmpoutput; \
	} > "$@"

$(addsuffix .log,$(wildcard interactive/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqtop) < "$<" 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	  fi; \
	} > "$@"

# Complexity test. Expects a line "(* Expected time < XXX.YYs *)" in
# the .v file with exactly two digits after the dot. The reference for
# time is a 6120 bogomips cpu.
ifneq (,$(bogomips))
$(addsuffix .log,$(wildcard complexity/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  true "extract effective user time"; \
	  res=`$(command) "$<" 2>&1 | sed -n -e "s/Finished transaction in .*(\([0-9]*\.[0-9]*\)u.*)/\1/p" | head -1`; \
	  R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)" ; \
	  elif [ "$$res" = "" ]; then \
	    echo $(log_failure); \
	    echo "    $<...Error! (couldn't find a time measure)"; \
	  else \
	    true "express effective time in centiseconds"; \
	    res=`echo "$$res"00 | sed -n -e "s/\([0-9]*\)\.\([0-9][0-9]\).*/\1\2/p"`; \
	    true "find expected time * 100"; \
	    exp=`sed -n -e "s/(\*.*Expected time < \([0-9]\).\([0-9][0-9]\)s.*\*)/\1\2/p" "$<"`; \
	    ok=`expr \( $$res \* $(bogomips) \) "<" \( $$exp \* 6120 \)`; \
	    if [ "$$ok" = 1 ]; then \
	      echo $(log_success); \
	      echo "    $<...Ok"; \
	    else \
	      echo $(log_failure); \
	      echo "    $<...Error! (should run faster)"; \
	    fi; \
	  fi; \
	} > "$@"
endif

# Ideal-features tests
$(addsuffix .log,$(wildcard ideal-features/*.v)): %.v.log: %.v
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(command) "$<" 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	      echo $(log_success); \
	      echo "    $<...still wished"; \
          else \
	      echo $(log_failure); \
	      echo "    $<...Good news! (wish seems to be granted, please check)"; \
          fi; \
	} > "$@"

# Additionnal dependencies for module tests
$(addsuffix .log,$(wildcard modules/*.v)): %.v.log: modules/Nat.vo modules/plik.vo
%.vo: %.v
	$(HIDE)$(coqtop) -compile $*

#######################################################################
# Miscellaneous tests
#######################################################################

misc: misc/xml.log misc/deps-order.log

# Test xml compilation
xml: misc/xml.log
misc/xml.log:
	@echo "TEST      misc/xml"
	$(HIDE){ \
	  echo $(call log_intro,xml); \
	  rm -rf misc/xml; \
	  COQ_XML_LIBRARY_ROOT=misc/xml \
	  $(bincoqc) -xml misc/berardi_test 2>&1; times; \
	  if [ ! -d misc/xml ]; then \
	    echo $(log_failure); \
	    echo "    misc/xml... failed"; \
	  else \
	    echo $(log_success); \
	    echo "    misc/xml...apparently ok"; \
	  fi; rm -r misc/xml; \
	} > "$@"

# Check that both coqdep and coqtop/coqc takes the later -I/-R
# Check that both coqdep and coqtop/coqc supports both -R and -I dir -as lib
# See bugs 2242, 2337, 2339
deps-order: misc/deps-order.log
misc/deps-order.log:
	@echo "TEST      misc/deps-order"
	$(HIDE){ \
	  echo $(call log_intro,deps-order); \
	  rm -f misc/deps/*/*.vo; \
	  tmpoutput=`mktemp /tmp/coqcheck.XXXXXX`; \
	  $(coqdep) -I misc/deps/lib -as lib -R misc/deps/client client misc/deps/client/bar.v 2>&1 \
	    | head -n 1 > $$tmpoutput; \
	  diff $$tmpoutput misc/deps/deps.out 2>&1; R=$$?; times; \
	  $(bincoqc) -I misc/deps/lib -as lib misc/deps/lib/foo.v 2>&1; \
	  $(bincoqc) -I misc/deps/lib -as lib -R misc/deps/client client misc/deps/client/foo.v 2>&1; \
	  $(coqtop) -I misc/deps/lib -as lib -R misc/deps/client client -load-vernac-source misc/deps/client/bar.v 2>&1; \
	  S=$$?; times; \
	  if [ $$R = 0 -a $$S = 0 ]; then \
	    echo $(log_success); \
	    echo "    misc/deps-order...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    misc/deps-order...Error! (unexpected order)"; \
	  fi; \
	  rm $$tmpoutput; \
	} > "$@"
