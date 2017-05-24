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
LIB := $(shell cd ..; pwd)

coqtop := $(BIN)coqtop -boot -q -batch -test-mode -R prerequisite TestSuite
coqc := $(BIN)coqc -coqlib $(LIB) -R prerequisite TestSuite
coqchk := $(BIN)coqchk -coqlib $(LIB) -R prerequisite TestSuite
coqtopbyte := $(BIN)coqtop.byte

coqtopload := $(coqtop) -top Top -async-proofs-cache force -load-vernac-source
coqtopcompile := $(coqtop) -compile
coqdep := $(BIN)coqdep -coqlib $(LIB)

SHOW := $(if $(VERBOSE),@true,@echo)
HIDE := $(if $(VERBOSE),,@)
REDIR := $(if $(VERBOSE),,> /dev/null 2>&1)

# read out an emacs config and look for coq-prog-args; if such exists, return it
get_coq_prog_args_helper = sed -n s'/^.*coq-prog-args:[[:space:]]*(\([^)]*\)).*/\1/p' $(1)
get_coq_prog_args = $(strip $(filter-out "-emacs-U" "-emacs",$(shell $(call get_coq_prog_args_helper,$(1)))))
SINGLE_QUOTE="
#" # double up on the quotes, in a comment, to appease the emacs syntax highlighter
# wrap the arguments in parens, but only if they exist
get_coq_prog_args_in_parens = $(subst $(SINGLE_QUOTE),,$(if $(call get_coq_prog_args,$(1)), ($(call get_coq_prog_args,$(1)))))
# get the command to use with this set of arguments; if there's -compile, use coqc, else use coqtop
has_compile_flag = $(filter "-compile",$(call get_coq_prog_args,$(1)))
has_profile_ltac_or_compile_flag = $(filter "-profile-ltac-cutoff" "-profile-ltac" "-compile",$(call get_coq_prog_args,$(1)))
get_command_based_on_flags = $(if $(call has_profile_ltac_or_compile_flag,$(1)),$(coqtopcompile),$(coqtopload))


bogomips:=
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
log_segfault = "==========> FAILURE <=========="
log_anomaly = "==========> FAILURE <=========="
log_failure = "==========> FAILURE <=========="
log_intro = "==========> TESTING $(1) <=========="

#######################################################################
# Testing subsystems
#######################################################################

# Apart so that it can be easily skipped with overriding
COMPLEXITY := $(if $(bogomips),complexity)

BUGS := bugs/opened bugs/closed

VSUBSYSTEMS := prerequisite success failure $(BUGS) output \
  output-modulo-time interactive micromega $(COMPLEXITY) modules stm

# All subsystems
SUBSYSTEMS := $(VSUBSYSTEMS) misc bugs ide vio coqchk

PREREQUISITELOG = prerequisite/admit.v.log			\
  prerequisite/make_local.v.log prerequisite/make_notation.v.log

#######################################################################
# Phony targets
#######################################################################

.DELETE_ON_ERROR:
.PHONY: all run clean $(SUBSYSTEMS)

all: run
	$(MAKE) report

run: $(SUBSYSTEMS)
bugs: $(BUGS)

clean:
	rm -f trace .lia.cache
	$(SHOW) "RM        <**/*.stamp> <**/*.vo> <**/*.vio> <**/*.log>"
	$(HIDE)find . \( \
	  -name '*.stamp' -o -name '*.vo' -o -name '*.vio' -o -name '*.log' \
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

summary_dir = echo $(1); find $(2) -name '*.log' -print0 | xargs -0 -n 1 tail -n1 | sort

.PHONY: summary summary.log

summary:
	@{ \
	  $(call summary_dir, "Preparing tests", prerequisite); \
	  $(call summary_dir, "Success tests", success); \
	  $(call summary_dir, "Failure tests", failure); \
	  $(call summary_dir, "Bugs tests", bugs); \
	  $(call summary_dir, "Output tests", output); \
	  $(call summary_dir, "Output (modulo time changes) tests", output-modulo-time); \
	  $(call summary_dir, "Interactive tests", interactive); \
	  $(call summary_dir, "Micromega tests", micromega); \
	  $(call summary_dir, "Miscellaneous tests", misc); \
	  $(call summary_dir, "Complexity tests", complexity); \
	  $(call summary_dir, "Module tests", modules); \
	  $(call summary_dir, "STM tests", stm); \
	  $(call summary_dir, "IDE tests", ide); \
	  $(call summary_dir, "VI tests", vio); \
	  $(call summary_dir, "Coqchk tests", coqchk); \
	  nb_success=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_success) | wc -l`; \
	  nb_failure=`find . -name '*.log' -exec tail -n2 '{}' \; | grep -e $(log_failure) | wc -l`; \
	  nb_tests=`expr $$nb_success + $$nb_failure`; \
	  pourcentage=`expr 100 \* $$nb_success / $$nb_tests`; \
	  echo; \
	  echo "$$nb_success tests passed over $$nb_tests, i.e. $$pourcentage %"; \
	}

summary.log:
	$(SHOW) BUILDING SUMMARY FILE
	$(HIDE)$(MAKE) --quiet summary > "$@"

report: summary.log
	$(HIDE)if grep -q -F 'Error!' summary.log ; then echo FAILURES; grep -F 'Error!' summary.log; false; else echo NO FAILURES; fi

#######################################################################
# Regression (and progression) tests
#######################################################################

# Process verifications concerning submitted bugs. A message is
# printed for all opened bugs (still active or seems to be closed).
# For closed bugs that behave as expected, no message is printed

# All files are assumed to have <# of the bug>.v as a name

# Opened bugs that should not fail
$(addsuffix .log,$(wildcard bugs/opened/*.v)): %.v.log: %.v
	@echo "TEST      $<  $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...still active"; \
	  elif [ $$R = 129 ]; then \
	    echo $(log_anomaly); \
	    echo "    $<...still active"; \
	  elif [ $$R = 139 ]; then \
	    echo $(log_segfault); \
	    echo "    $<...still active"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be closed, please check)"; \
	  fi; \
	} > "$@"

# Closed bugs that should succeed
$(addsuffix .log,$(wildcard bugs/closed/*.v)): %.v.log: %.v
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
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
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqtopcompile) "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be prepared" ; \
	  else \
	    echo $(log_success); \
	    echo "    $<...correctly prepared" ; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard success/*.v micromega/*.v modules/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  opts="$(if $(findstring modules/,$<),-R modules Mods -impredicative-set)"; \
	  echo $(call log_intro,$<); \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") $$opts 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	  fi; \
	} > "$@"

stm: $(wildcard stm/*.v:%.v=%.v.log)
$(addsuffix .log,$(wildcard stm/*.v)): %.v.log: %.v
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqtopcompile) "$<" $(call get_coq_prog_args,"$<") -async-proofs on \
	    $$opts 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard failure/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be rejected)"; \
	  fi; \
	} > "$@"

$(addsuffix .log,$(wildcard output/*.v)): %.v.log: %.v %.out $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  tmpoutput=`mktemp /tmp/coqcheck.XXXXXX`; \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1 \
	    | grep -v "Welcome to Coq" \
	    | grep -v "\[Loading ML file" \
	    | grep -v "Skipping rcfile loading" \
	    | grep -v "^<W>" \
	    | sed 's/File "[^"]*"/File "stdin"/' \
	    > $$tmpoutput; \
	  diff -u $*.out $$tmpoutput 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	  fi; \
	  rm $$tmpoutput; \
	} > "$@"

$(addsuffix .log,$(wildcard output-modulo-time/*.v)): %.v.log: %.v %.out
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  tmpoutput=`mktemp /tmp/coqcheck.XXXXXX`; \
	  tmpexpected=`mktemp /tmp/coqcheck.XXXXXX`; \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1 \
	    | grep -v "Welcome to Coq" \
	    | grep -v "\[Loading ML file" \
	    | grep -v "Skipping rcfile loading" \
	    | grep -v "^<W>" \
	    | sed -e 's/\s*[-+0-9]*\.[0-9][0-9]*\s*//g' \
	          -e 's/\s*0\.\s*//g' \
		  -e 's/\s*[-+]nan\s*//g' \
		  -e 's/\s*[-+]inf\s*//g' \
		  -e 's/^[^a-zA-Z]*//' \
	    | sort \
	    > $$tmpoutput; \
	  sed -e 's/\s*[-+0-9]*\.[0-9][0-9]*\s*//g' \
		-e 's/\s*0\.\s*//g' \
		-e 's/\s*[-+]nan\s*//g' \
		-e 's/\s*[-+]inf\s*//g' \
		-e 's/^[^a-zA-Z]*//' \
	       $*.out | sort > $$tmpexpected; \
	  diff -b -u $$tmpexpected $$tmpoutput 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	  fi; \
	  rm $$tmpoutput; \
	  rm $$tmpexpected; \
	} > "$@"

$(addsuffix .log,$(wildcard interactive/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqtop) $(call get_coq_prog_args,"$<") < "$<" 2>&1; R=$$?; times; \
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
$(addsuffix .log,$(wildcard complexity/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  true "extract effective user time"; \
	  res=`$(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1 | sed -n -e "s/Finished transaction in .*(\([0-9]*\.[0-9]*\)u.*)/\1/p" | head -1`; \
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
$(addsuffix .log,$(wildcard ideal-features/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call get_command_based_on_flags,"$<") "$<" $(call get_coq_prog_args,"$<") 2>&1; R=$$?; times; \
	  if [ $$R != 0 ]; then \
	      echo $(log_success); \
	      echo "    $<...still wished"; \
          else \
	      echo $(log_failure); \
	      echo "    $<...Good news! (wish seems to be granted, please check)"; \
          fi; \
	} > "$@"

# Additional dependencies for module tests
$(addsuffix .log,$(wildcard modules/*.v)): %.v.log: modules/Nat.vo modules/plik.vo
modules/%.vo: modules/%.v
	$(HIDE)$(coqtop) -R modules Mods -compile $<

#######################################################################
# Miscellaneous tests
#######################################################################

misc: $(patsubst %.sh,%.log,$(wildcard misc/*.sh))

misc/universes.log: misc/universes/all_stdlib.v

misc/universes/all_stdlib.v:
	cd .. && $(MAKE) test-suite/$@

$(patsubst %.sh,%.log,$(wildcard misc/*.sh)): %.log: %.sh $(PREREQUISITELOG)
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  export coqc="$(coqc)"; \
	  export coqtop="$(coqtop)"; \
	  export coqdep="$(coqdep)"; \
	  export coqtopbyte="$(coqtopbyte)"; \
	  "$<" 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	  fi; \
	} > "$@"

# IDE : some tests of backtracking for coqtop -ideslave

ide : $(patsubst %.fake,%.fake.log,$(wildcard ide/*.fake))

%.fake.log : %.fake
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(BIN)fake_ide $< "$(BIN)coqtop -boot -async-proofs on -async-proofs-tactic-error-resilience off -async-proofs-command-error-resilience off" 2>&1; \
	  if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	  fi; \
	} > "$@"

vio: $(patsubst %.v,%.vio.log,$(wildcard vio/*.v))

%.vio.log:%.v
	@echo "TEST      $<"
	$(HIDE){ \
	  $(coqc) -quick -R vio vio $* 2>&1 && \
	  $(coqtop) -R vio vio -vio2vo $*.vio 2>&1 && \
	  $(coqchk) -R vio vio -norec $(subst /,.,$*) 2>&1; \
	  if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	  fi; \
	} > "$@"

coqchk: $(patsubst %.v,%.chk.log,$(wildcard coqchk/*.v))

%.chk.log:%.v
	@echo "TEST      $<"
	$(HIDE){ \
	  $(coqc) -R coqchk coqchk $* 2>&1 && \
	  $(coqchk) -R coqchk coqchk -norec $(subst /,.,$*) 2>&1; \
	  if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	  fi; \
	} > "$@"
