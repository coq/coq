##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
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

###########################################################################
# Includes, see below for generation
###########################################################################

# Generate test-suite, when INSIDE_DUNE the file is guaranteed to
# exist, when called directly by make we need to look into the build
# directory.
DUNE_CONTEXT:=default
TEST_SUITE_CONFIG_FILE:=test_suite_config.inc

ifeq ($(INSIDE_DUNE),)
TEST_SUITE_CONFIG_PATH:=../_build/$(DUNE_CONTEXT)/test-suite/$(TEST_SUITE_CONFIG_FILE)
else
TEST_SUITE_CONFIG_PATH:=$(TEST_SUITE_CONFIG_FILE)
endif

include $(TEST_SUITE_CONFIG_PATH)

#######################################################################
# Variables
#######################################################################

# COQPREFIX is quoted to anticipate the possibility of spaces in the directory name
# Note that this will later need an eval in shell to interpret the quotes
BIN:=$(COQPREFIX)/bin/

# An alternative is ifeq ($(OS),Windows_NT) using make's own variable.
ifeq ($(ARCH),win32)
  export FINDLIB_SEP=;
else
  export FINDLIB_SEP=:
endif

# The $(shell echo) trick is necessary due to configure quoting
# filenames, still, this issue is tricky when paths contain spaces
export OCAMLPATH := $(shell echo $(COQPREFIX)/lib$(FINDLIB_SEP)$$OCAMLPATH)
export CAML_LD_LIBRARY_PATH:=$(shell echo $(COQPREFIX)/lib/stublibs):$(CAML_LD_LIBRARY_PATH)

# ROCQLIB is an env variable so no quotes
ROCQLIB?=

ifeq ($(ROCQLIB),)
# Guard againt the COQLIBINSTALL directory not existing, otherwise
# ocaml_pwd will error
ifneq ($(wildcard $(shell echo $(COQLIBINSTALL))),)
	ROCQLIB := $(shell ocaml ocaml_pwd.ml $(COQLIBINSTALL))
endif
endif
export ROCQLIB

ifeq ($(wildcard $(ROCQLIB)/theories/Init/Prelude.vo),)
  COQLIB_NOT_FOUND:=true
else
  COQLIB_NOT_FOUND:=false
endif

COQEXTRAFLAGS?=
COQFLAGS?=$(COQEXTRAFLAGS)

coqc := $(BIN)rocq c -q -R prerequisite TestSuite $(COQFLAGS)
coqchk := $(BIN)rocqchk -R prerequisite TestSuite
coqdoc := $(BIN)rocq doc
coqtop := $(BIN)rocq repl -q -test-mode -R prerequisite TestSuite

coqidetop := $(BIN)coqidetop

coqc_interactive := $(coqc) -test-mode
coqdep := $(BIN)rocq dep

# This is the convention for coq_makefile
OPT=-$(BEST)
export OPT

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
INTERACTIVE := interactive
UNIT_TESTS := unit-tests
VSUBSYSTEMS := prerequisite success failure bugs bugs-nocoqchk output output-coqtop \
  output-modulo-time $(INTERACTIVE) $(COMPLEXITY) modules stm \
  coqdoc ssr $(wildcard primitive/*) ltac2 coqchk

# All subsystems
SUBSYSTEMS := $(VSUBSYSTEMS) misc ide ide coqchk output-coqchk coqwc coq-makefile precomputed-time-tests tools $(UNIT_TESTS)

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
	@echo "Coq's standard library has not been built; please run: "
	@echo "  - make world"
	@echo ""
	@false
else
ifeq ($(TIMED),)
all: run
	$(MAKE) report
else
all:
	$(MAKE) run | tee time-of-build.log
	python ../tools/make-one-time-file.py --real time-of-build.log
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
	  $(call summary_dir, "Failure tests", failure); \
	  $(call summary_dir, "Bugs tests", bugs); \
	  $(call summary_dir, "Bugs tests (no coqchk)", bugs-nocoqchk); \
	  $(call summary_dir, "Output tests", output); \
	  $(call summary_dir, "Output tests with coqtop", output-coqtop); \
	  $(call summary_dir, "Output (modulo time changes) tests", output-modulo-time); \
	  $(call summary_dir, "Interactive tests", interactive); \
	  $(call summary_dir, "Miscellaneous tests", misc); \
	  $(call summary_dir, "Complexity tests", complexity); \
	  $(call summary_dir, "Module tests", modules); \
	  $(call summary_dir, "Primitive tests", primitive); \
	  $(call summary_dir, "STM tests", stm); \
	  $(call summary_dir, "SSR tests", ssr); \
	  $(call summary_dir, "IDE tests", ide); \
	  $(call summary_dir, "Coqchk tests", coqchk); \
	  $(call summary_dir, "Output tests with coqchk", output-coqchk); \
	  $(call summary_dir, "Coqwc tests", coqwc); \
	  $(call summary_dir, "Coq makefile", coq-makefile); \
	  $(call summary_dir, "Precomputed time tests", precomputed-time-tests); \
	  $(call summary_dir, "Coqdoc tests", coqdoc); \
	  $(call summary_dir, "tools/ tests", tools); \
	  $(call summary_dir, "Unit tests", unit-tests); \
	  $(call summary_dir, "Ltac2 tests", ltac2); \
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
# Test suite configuration, to eventually go away
#######################################################################

# Not inside Dune, build by hand, note the shuffling
ifeq ($(INSIDE_DUNE),)
$(TEST_SUITE_CONFIG_PATH):
	dune build $(TEST_SUITE_CONFIG_FILE)
endif

#######################################################################
# Unit tests
#######################################################################

# COQLIBINSTALL is quoted in config/make thus we must unquote it,
# otherwise the directory name will include the quotes, see
# see for example https://stackoverflow.com/questions/10424645/how-to-convert-a-quoted-string-to-a-normal-one-in-makefile

OCAMLOPT := $(OCAMLFIND) opt $(CAMLFLAGS)
OCAMLC := $(OCAMLFIND) ocamlc $(CAMLFLAGS)

# ML files from unit-test framework, not containing tests
UNIT_SRCFILES:=$(shell find ./unit-tests/src -name '*.ml')
UNIT_ALLMLFILES:=$(shell find ./unit-tests -name '*.ml')
UNIT_MLFILES:=$(filter-out $(UNIT_SRCFILES),$(UNIT_ALLMLFILES))
UNIT_LOGFILES:=$(patsubst %.ml,%.ml.log,$(UNIT_MLFILES))

ifneq ($(BEST),opt)
UNIT_LINK:=utest.cmo
OCAMLBEST:=$(OCAMLC)
else
UNIT_LINK:=utest.cmx
OCAMLBEST:=$(OCAMLOPT)
endif

unit-tests/src/utest.cmx: unit-tests/src/utest.ml unit-tests/src/utest.cmi
	$(SHOW) 'OCAMLOPT  $<'
	$(HIDE)$(OCAMLOPT) -c -I unit-tests/src -package ounit2 $<
unit-tests/src/utest.cmo: unit-tests/src/utest.ml unit-tests/src/utest.cmi
	$(SHOW) 'OCAMLC  $<'
	$(HIDE)$(OCAMLC) -c -I unit-tests/src -package ounit2 $<
unit-tests/src/utest.cmi: unit-tests/src/utest.mli
	$(SHOW) 'OCAMLC  $<'
	$(HIDE)$(OCAMLC) -package ounit2 -c $<

unit-tests: $(UNIT_LOGFILES)

# Build executable, run it to generate log file
unit-tests/%.ml.log: unit-tests/%.ml unit-tests/src/$(UNIT_LINK)
	$(SHOW) 'TEST      $<'
	$(HIDE)$(OCAMLBEST) -w -29 -linkpkg -package rocq-runtime.toplevel,ounit2 \
	     -I unit-tests/src $(UNIT_LINK) $< -o $<.test;
	$(HIDE)$(call WITH_TIMER,$@,./$<.test)
	$(HIDE)$(call REPORT_TIMER,$@)

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

$(addsuffix .log,$(wildcard bugs/*.v ssr/*.v success/*.v failure/*.v stm/*.v modules/*.v primitive/*/*.v ltac2/*.v coqchk/*.v)): %.v.log: %.v $(PREREQUISITELOG)
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

# coqchk shouldn't be run on the result for various reasons (not yet fixed bug, using -vos, etc)
$(addsuffix .log,$(wildcard bugs-nocoqchk/*.v)): %.v.log: %.v
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1); R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (bug seems to be opened, please check)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

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
	  } | grep -a -v "Welcome to Rocq" \
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

$(addsuffix .log,$(wildcard output-coqtop/*.v)): %.v.log: %.v %.out $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  output=$*.out.real; \
	  $(call WITH_TIMER,$@,$(coqtop) < "$<" $(call get_coq_prog_args,"$<") 2>&1) \
	    | grep -v "Welcome to Rocq" \
	    | grep -v "\[Loading ML file" \
	    | grep -v "Skipping rcfile loading" \
	    | grep -v "^<W>" \
	    > $$output; \
	  diff -u --strip-trailing-cr $*.out $$output 2>&1; R=$$?; times; \
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

output-coqchk: $(addsuffix .log,$(wildcard output-coqchk/*.v))
$(addsuffix .log,$(wildcard output-coqchk/*.v)): %.v.log: %.v %.out $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1); R=$$?; times; \
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
	  echo $(call log_intro,$<); \
	  output=$*.out.real; \
	  export LC_CTYPE=C; \
	  export LANG=C; \
	  $(call WITH_TIMER,$(patsubst %.v.log,%.chk.log,$@),$(coqchk) -o -silent $(call get_coqchk_prog_args,"$<") -Q $(shell dirname $<) "" -norec $(shell basename $< .v) > $$output 2>&1) ; \
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
	} > "$(shell dirname $<)/$(shell basename $< .v).chk.log"; fi
	$(HIDE)$(call REPORT_TIMER,$(patsubst %.v.log,%.chk.log,$@))

.PHONY: approve-output
approve-output: output output-coqtop output-coqchk
	$(HIDE)for f in $(addsuffix /*.out.real,$^); do if [ -f "$$f" ]; then \
	  mv "$$f" "$${f%.real}"; \
	  echo "Updated $${f%.real}!"; \
	fi; done

approve-coqdoc: coqdoc
	$(HIDE)(cd coqdoc; \
	for f in *.html.out; do if [ -f "$$f" ]; then \
	  cp "Coqdoc.$${f%.out}" "$$f"; \
	  echo "Updated $$f!"; \
	fi; done; \
	for f in *.tex.out; do if [ -f "$$f" ]; then \
	  cat "Coqdoc.$${f%.out}" | grep -v "^%%" > "$$f"; \
	  echo "Updated $$f!"; \
	fi; done)

$(addsuffix .log,$(wildcard output-modulo-time/*.v)): %.v.log: %.v %.out
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  tmpoutput=`mktemp`; \
	  tmpexpected=`mktemp`; \
	  $(call WITH_TIMER,$@,$(coqc_interactive) "$<" $(call get_coq_prog_args,"$<") 2>&1) \
	    | grep -v "Welcome to Rocq" \
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
	  diff  --strip-trailing-cr -b -u $$tmpexpected $$tmpoutput 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	    $(FAIL); \
	  fi; \
	  rm $$tmpoutput; \
	  rm $$tmpexpected; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

$(addsuffix .log,$(wildcard interactive/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqtop) $(call get_coq_prog_args,"$<") < "$<" 2>&1); R=$$?; times; \
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

# Ideal-features tests
$(addsuffix .log,$(wildcard ideal-features/*.v)): %.v.log: %.v $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,$(coqc) "$<" $(call get_coq_prog_args,"$<") 2>&1); R=$$?; times; \
	  if [ $$R != 0 ]; then \
	      echo $(log_success); \
	      echo "    $<...still wished"; \
          else \
	      echo $(log_failure); \
	      echo "    $<...Good news! (wish seems to be granted, please check)"; \
	      $(FAIL); \
          fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

# Additional dependencies for module tests
COMMON_MODULE_DEPENDENCIES := modules/plik.v
# We exclude plik.v.log because this log file does not
# depend on having the corresponding .vo file built first, and we end
# up with pseudo-cyclic build rules if we don't exclude it (See
# COQBUG(https://github.com/coq/coq/issues/12582)).
$(addsuffix .log,$(filter-out $(COMMON_MODULE_DEPENDENCIES),$(wildcard modules/*.v))): %.v.log: $(COMMON_MODULE_DEPENDENCIES:.v=.v.log)

#######################################################################
# Miscellaneous tests
#######################################################################

misc: $(patsubst %.sh,%.log,$(wildcard misc/*.sh))

misc/universes.log: misc/universes/all_stdlib.v

misc/universes/all_stdlib.v:
	cd misc/universes && ./build_all_stdlib.sh > all_stdlib.v

$(patsubst %.sh,%.log,$(wildcard misc/*.sh)): %.log: %.sh $(PREREQUISITELOG)
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  export BIN=$(BIN); \
	  export coqc="eval $(coqc)"; \
	  export coqdep="eval $(coqdep)"; \
	  $(call WITH_TIMER,$@,"$<" 2>&1); R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

# IDE : some tests of backtracking for coqtop -ideslave

ide : $(patsubst %.fake,%.fake.log,$(wildcard ide/*.fake))

ide/fake_ide.exe : ide/fake_ide.ml
	$(SHOW) 'OCAMLC  $<'
	$(HIDE)$(OCAMLBEST) -linkpkg -package coqide-server.protocol -package coqide-server.core $< -o $@

%.fake.log : %.fake ide/fake_ide.exe
	@echo "TEST      $<"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(call WITH_TIMER,$@,ide/fake_ide.exe $(coqidetop) "$<" "-q -async-proofs on -async-proofs-tactic-error-resilience off -async-proofs-command-error-resilience off $(call get_coq_prog_args,"$<")" 2>&1); \
	  if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	    $(FAIL); \
	  fi; \
	} > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

# coqwc : test output

coqwc : $(patsubst %.v,%.v.log,$(wildcard coqwc/*.v))

coqwc/%.v.log : coqwc/%.v
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  tmpoutput=`mktemp`; \
	  $(BIN)rocq wc $< 2>&1 > $$tmpoutput; \
	  diff -u --strip-trailing-cr coqwc/$*.out $$tmpoutput 2>&1; R=$$?; times; \
	  if [ $$R = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	    $(FAIL); \
	  fi; \
	  rm $$tmpoutput; \
	} > "$@"

# coq_makefile and precomputed time tests

coq-makefile: $(patsubst %/run.sh,%.log,$(wildcard coq-makefile/*/run.sh))
precomputed-time-tests: $(patsubst %/run.sh,%.log,$(wildcard precomputed-time-tests/*/run.sh))

$(patsubst %/run.sh,%.log,$(wildcard coq-makefile/*/run.sh precomputed-time-tests/*/run.sh)): %.log: %/run.sh
	@echo "TEST      $*"
	$(HIDE)(\
	  export COQBIN=$(BIN);\
	  export COQPREFIX=$(COQPREFIX);\
	  cd $* && \
	  $(call WITH_TIMER,$@,bash run.sh 2>&1,../../$@.time); \
	if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	    $(FAIL); \
	  fi; \
	) > "$@"
	$(HIDE)$(call REPORT_TIMER,$@)

# coqdoc

$(addsuffix .log,$(wildcard coqdoc/*.v)): %.v.log: %.v %.html.out %.tex.out $(PREREQUISITELOG)
	@echo "TEST      $< $(call get_coq_prog_args_in_parens,"$<")"
	$(HIDE){ \
	  echo $(call log_intro,$<); \
	  $(coqc) -R coqdoc Coqdoc $* 2>&1; \
	  cd coqdoc; \
	  f=`basename $*`; \
	  $(coqdoc) -utf8 -R . Coqdoc -coqlib_url http://coq.inria.fr/stdlib --html $$f.v 2>&1; \
	  $(coqdoc) -utf8 -R . Coqdoc -coqlib_url http://coq.inria.fr/stdlib --latex $$f.v 2>&1; \
	  diff -u --strip-trailing-cr $$f.html.out Coqdoc.$$f.html 2>&1; R=$$?; times; \
	  grep -v "^%%" Coqdoc.$$f.tex | diff -u --strip-trailing-cr $$f.tex.out - 2>&1; S=$$?; times; \
	  if [ $$R = 0 -a $$S = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error! (unexpected output)"; \
	    $(FAIL); \
	  fi; \
	} > "$@"

# tools/

tools: $(patsubst %/run.sh,%.log,$(wildcard tools/*/run.sh))

tools/%.log : tools/%/run.sh
	@echo "TEST      tools/$*"
	$(HIDE)(\
	  export COQBIN=$(BIN);\
	  cd tools/$* && \
	  bash run.sh 2>&1; \
	if [ $$? = 0 ]; then \
	    echo $(log_success); \
	    echo "    $<...Ok"; \
	  else \
	    echo $(log_failure); \
	    echo "    $<...Error!"; \
	    $(FAIL); \
	  fi; \
	) > "$@"
