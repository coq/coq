#!/usr/bin/env bash

set -x
set -e
set -o pipefail

export PATH="$COQBIN:$PATH"
export LC_ALL=C

# tools
TTOOLSDIR="$COQPREFIX/lib/rocq-runtime/tools"

export make_both_time_files="$TTOOLSDIR"/make-both-time-files.py
export make_one_time_file="$TTOOLSDIR"/make-one-time-file.py
export make_both_single_timing_files="$TTOOLSDIR"/make-both-single-timing-files.py

# native stack overflows too easily, see eg
# https://gitlab.com/coq/coq/-/jobs/3250939810
export COQEXTRAFLAGS='-native-compiler no'

# reset MAKEFLAGS so that, e.g., `make -C test-suite -B coq-makefile` doesn't give us issues

MAKEFLAGS=
