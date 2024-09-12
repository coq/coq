##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################

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

# An alternative is ifeq ($(OS),Windows_NT) using make's own variable.
ifeq ($(ARCH),win32)
  export FINDLIB_SEP=;
else
  export FINDLIB_SEP=:
endif

COQEXTRAFLAGS?=
COQFLAGS?=$(COQEXTRAFLAGS)

coqc := coqc -q -R prerequisite TestSuite $(COQFLAGS)
coqchk := coqchk -R prerequisite TestSuite
coqdoc := coqdoc
coqtop := coqtop -q -test-mode -R prerequisite TestSuite
coqtopbyte := coqtop.byte -q

coqc_interactive := $(coqc) -test-mode

COQLIB_NOT_FOUND := $(shell (echo "From Stdlib Require Reals." > tmp_test.v && coqc tmp_test.v > /dev/null 2>&1 && rm -f tmp_test.* && echo "false") || (rm -f tmp_test.* && echo "true"))

VERBOSE?=
SHOW := $(if $(VERBOSE),@true,@echo)
HIDE := $(if $(VERBOSE),,@)
REDIR := $(if $(VERBOSE),,> /dev/null 2>&1)

# per test timing support (copied from CoqMakefile.in)
TIMED?=
TIMEFMT?="$(1) (real: %e, user: %U, sys: %S, mem: %M ko)"

ifneq (,$(TIMED))
ifeq (0,$(shell command time -f "" true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=command time --quiet -f $(TIMEFMT) -o $(2)
else
ifeq (0,$(shell gtime --quiet -f "" true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=gtime -f $(TIMEFMT) -o $(2)
else
STDTIME?=command time
endif
endif
else
STDTIME?=command time -f $(TIMEFMT) -o $(2)
endif

# args: 1=name of target, 2=command to time,
# 3=file to write time data to (optional, default $(1).time)
WITH_TIMER=$(if $(TIMED), $(call STDTIME,$(1),$(if $(3),$(3),$(1).time)) $(2), $(2))

REPORT_TIMER=$(if $(TIMED),$(foreach f,$(1),cat $(f).time 2>/dev/null || true;),:)

# read out an emacs config and look for coq-prog-args; if such exists, return it
get_coq_prog_args_helper = sed -n s'/^.*$(1):[[:space:]]*(\([^)]*\)).*/\1/p' $(2)
get_coq_prog_args = $(strip $(shell $(call get_coq_prog_args_helper,coq-prog-args,$(1))))
get_coqchk_prog_args = $(strip $(shell $(call get_coq_prog_args_helper,coqchk-prog-args,$(1))) $(filter "-impredicative-set",$(call get_coq_prog_args,$(1))))
SINGLE_QUOTE="
#" # double up on the quotes, in a comment, to appease the emacs syntax highlighter
# wrap the arguments in parens, but only if they exist
get_coq_prog_args_in_parens = $(subst $(SINGLE_QUOTE),,$(if $(call get_coq_prog_args,$(1)), ($(call get_coq_prog_args,$(1)))))
get_coqchk_prog_args_in_parens = $(subst $(SINGLE_QUOTE),,$(if $(call get_coqchk_prog_args,$(1)), ($(call get_coqchk_prog_args,$(1)))))

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

# keep these synced with test-suite/save-logs.sh
log_success = "==========> SUCCESS <=========="
log_segfault = "==========> FAILURE <=========="
log_anomaly = "==========> FAILURE <=========="
log_failure = "==========> FAILURE <=========="
log_intro = "==========> TESTING $(1) <=========="

FAIL = >&2 echo 'FAILED    $@'
FAIL_CHK = >&2 echo 'FAILED    $(patsubst %.v.log,%.chk.log,$@)'

#######################################################################
# Testing subsystems
#######################################################################

# These targets can be skipped by doing `make TARGET= test-suite`
COMPLEXITY := $(if $(bogomips),complexity)
VSUBSYSTEMS := prerequisite success bugs output \
  micromega $(COMPLEXITY) modules stm

# All subsystems
SUBSYSTEMS := $(VSUBSYSTEMS)

# EJGA: This seems dangerous as first target...
.csdp.cache: .csdp.cache.test-suite
	cp $< $@
	chmod u+w $@

PREREQUISITELOG = $(addsuffix .log,$(wildcard prerequisite/*.v)) .csdp.cache

#######################################################################
# Phony targets
#######################################################################

.DELETE_ON_ERROR:
.PHONY: all run clean $(SUBSYSTEMS)

ifeq ($(COQLIB_NOT_FOUND),true)
all:
	@echo ""
	@echo "Coq's standard library has not been installed; please run: "
	@echo "  - make"
	@echo "  - make install"
	@echo ""
	@false
else
ifeq ($(TIMED),)
all: run
	$(MAKE) report
else
all:
	$(MAKE) run | tee time-of-build.log
	python ../../tools/make-one-time-file.py --real time-of-build.log
	$(MAKE) report
endif
endif

# do nothing
.PHONY: noop
noop: ;

run: $(SUBSYSTEMS)

clean:
	rm -f trace .csdp.cache .nia.cache .lia.cache
	rm -f misc/universes/all_stdlib.v
	$(SHOW) 'RM        <**/*.stamp> <**/*.vo> <**/*.log> <**/*.glob> <**/*.time>'
	$(HIDE)find . \( \
	  -name '*.stamp' -o -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.log' -o -name '*.glob' -o -name '*.time' \
	  \) -exec rm -f {} +
	$(SHOW) 'RM        <**/*.cmx> <**/*.cmi> <**/*.o> <**/*.test>'
	$(HIDE)find unit-tests \( \
	  -name '*.cmx' -o -name '*.cmi' -o -name '*.o' -o -name '*.test' \
	  \) -exec rm -f {} +
distclean: clean
	$(SHOW) 'RM        <**/*.aux>'
	$(HIDE)find . -name '*.aux' -exec rm -f {} +

#######################################################################
# Per-subsystem targets
#######################################################################

define vdeps
$(1): $(patsubst %.v,%.v.log,$(wildcard $(1)/*.v))
endef
$(foreach S,$(VSUBSYSTEMS),$(eval $(call vdeps,$(S))))

#######################################################################
# Summary
#######################################################################

# using "-L 999" because some versions of tail do not accept more than ~1k arguments
summary_dir = echo $(1); find $(2) -name '*.log' -print0 | xargs -0 -L 999  tail -q -n1 | sort

.PHONY: summary summary.log

summary:
	@{ \
	  $(call summary_dir, "Preparing tests", prerequisite); \
	  $(call summary_dir, "Success tests", success); \
	  $(call summary_dir, "Bugs tests", bugs); \
	  $(call summary_dir, "Output tests", output); \
	  $(call summary_dir, "Complexity tests", complexity); \
	  $(call summary_dir, "Module tests", modules); \
	  $(call summary_dir, "STM tests", stm); \
	  nb_success=`grep -e $(log_success) -r . -l --include="*.log" --exclude-dir=logs | wc -l`; \
	  nb_failure=`grep -e $(log_failure) -r . -l --include="*.log" --exclude-dir=logs | wc -l`; \
	  nb_tests=`expr $$nb_success + $$nb_failure`; \
	  percentage=`expr 100 \* $$nb_success / $$nb_tests`; \
	  echo; \
	  echo "$$nb_success tests passed over $$nb_tests, i.e. $$percentage %"; \
	}

summary.log:
	$(SHOW) BUILDING SUMMARY FILE
	$(HIDE)$(MAKE) --quiet summary > "$@"

report: summary.log
	$(HIDE)bash report.sh

#######################################################################
# Other generic tests
#######################################################################

prerequisite/requires_deprecated_library.v.log: prerequisite/deprecated_library.v.log

$(addsuffix .log,$(wildcard prerequisite/*.v)): %.v.log: %.v
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1); R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be prepared" ; \
	    $(FAIL); \
	  else \
	    echo $(log_success); \
	    echo "    $<...correctly prepared" ; \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

modules/PO.v.log: modules/Nat.v.log

$(addsuffix .log,$(wildcard bugs/*.v success/*.v stm/*.v micromega/*.v modules/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  opts="$(if $(findstring modules/,$<),-R modules Mods)"; \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqc) "$<" $(call get_coq_prog_args,"$<") $$opts 2>&1); R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)
	@if ! grep -q -F "Error!" $@; then echo "CHECK     $< $(call get_coqchk_prog_args_in_parens,"$<")"; fi
	$(HIDE)if ! grep -q -F "Error!" $@; then { \
	  $(call WITH_TIMER,$(patsubst %.v.log,%.chk.log,$@),\
	    $(coqchk) $(call get_coqchk_prog_args,"$<") \
	      $(if $(findstring modules/,$<), \
		-R modules Mods -norec Mods.$(shell basename $< .v), \
		-Q $(shell dirname $<) "" -norec $(shell basename $< .v)) 2>&1); R=$$?; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...could not be checked (Error!)" ; \
	    $(FAIL_CHK); \
	  fi; \
	} > "$(shell dirname $<)/$(shell basename $< .v).chk.log"; fi
	$(HIDE)$(call REPORT_TIMER,$(patsubst %.v.log,%.chk.log,$@))

$(addsuffix .log,$(wildcard output/*.v)): %.v.log: %.v %.out $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  output=$*.out.real; \
	  export LC_CTYPE=C; \
	  export LANG=C; \
	  { $(call WITH_TIMER,$@,$(coqc_interactive) "$<" $(call get_coq_prog_args,"$<") 2>&1); \
	      R=$$?; \
	      if ! [ $$R = 0 ]; then printf '\ncoqc exited with code %s\n' "$$R"; fi; \
	  } | grep -a -v "Welcome to Coq" \
	    | grep -a -v "\[Loading ML file" \
	    | grep -a -v "Skipping rcfile loading" \
	    | grep -a -v "^<W>" \
	    > $$output; \
	  diff -a -u --strip-trailing-cr $*.out $$output 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	    rm $$output; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

.PHONY: approve-output
approve-output: output output-coqtop output-coqchk
	$(HIDE)for f in $(addsuffix /*.out.real,$^); do if [ -f "$$f" ]; then \
	  mv "$$f" "$${f%.real}"; \
	  echo "Updated $${f%.real}!"; \
	fi; done

# Complexity test. Expects a line "(* Expected time < XXX.YYs *)" in
# the .v file with exactly two digits after the dot. The reference for
# time is a 6120 bogomips cpu.
ifneq (,$(bogomips))
$(addsuffix .log,$(wildcard complexity/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  true "extract effective user time"; \
	  res=`$(call WITH_TIMER,$@,$(coqc_interactive) "$<" $(call get_coq_prog_args,"$<") 2>&1) | sed -n -e "s/Finished .*transaction in .*(\([0-9]*\.[0-9]*\)u.*)/\1/p" | head -1 | sed "s/\r//g"`; \
	  R=$$?; times; \
	  if [ $$R != 0 ]; then \
	    echo $(log_failure); \
	    echo "    $<...Error! (should be accepted)" ; \
	    $(FAIL); \
	  elif [ "$$res" = "" ]; then \
	    echo $(log_failure); \
	    echo "    $<...Error! (couldn't find a time measure)"; \
	    $(FAIL); \
	  else \
	    true "express effective time in centiseconds"; \
	    resorig="$$res"; \
	    res=`echo "$$res"00 | sed -n -e "s/\([0-9]*\)\.\([0-9][0-9]\).*/\1\2/p"`; \
	    if [ "$$res" = "" ]; then \
	      echo $(log_failure); \
	      echo "    $<...Error! (invalid time measure: $$resorig)"; \
	    else \
	      true "find expected time * 100"; \
	      exp=`sed -n -e "s/(\*.*Expected time < \([0-9]\).\([0-9][0-9]\)s.*\*)/\1\2/p" "$<"`; \
	      true "compute corrected effective time, rounded up"; \
	      rescorrected=`expr \( $$res \* $(bogomips) + 6120 - 1 \) / 6120`; \
	      ok=`expr \( $$res \* $(bogomips) \) "<" \( $$exp \* 6120 \)`; \
	      if [ "$$ok" = 1 ]; then \
	        echo $(log_success); \
	        echo "    $<...Ok"; \
	      else \
	        echo $(log_failure); \
	        echo "    $<...Error! (should run faster ($$rescorrected >= $$exp))"; \
	        $(FAIL); \
	      fi; \
	    fi; \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)
endif
