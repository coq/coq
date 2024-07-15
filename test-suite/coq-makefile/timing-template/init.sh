#!/usr/bin/env bash

set -x
set -e

# native stack overflows too easily, see eg
# https://gitlab.com/coq/coq/-/jobs/3250939810
export COQEXTRAFLAGS='-native-compiler no'

. ../template/path-init.sh

# reset MAKEFLAGS so that, e.g., `make -C test-suite -B coq-makefile` doesn't give us issues

MAKEFLAGS=


INFINITY="∞"
INFINITY_REPLACEMENT="+.%" # assume that if the before time is zero, we expected the time to increase

TO_SED_IN_BOTH=(
    -e s"/${INFINITY}/${INFINITY_REPLACEMENT}/g" # Whether or not something shows up as ∞ depends on whether a time registers as 0.s or as 0.001s, so we can't rely on this being consistent
    -e s':|\s*N/A\s*$:| '"${INFINITY_REPLACEMENT}"':g' # Whether or not something shows up as N/A depends on whether a time registers as 0.s or as 0.001s, so we can't rely on this being consistent
    -e s'/ *$//g' # the number of trailing spaces depends on how many digits percentages end up being; since this varies across runs, we remove trailing spaces
    -e s'/[0-9]*\.[0-9]*//g' # the precise timing numbers vary, so we strip them out
    -e s'/^-*$/------/g' # When none of the numbers get over 100 (or 1000, in per-file), the width of the table is different, so we normalize the number of dashes for table separators
    -e s'/+/-/g' # some code lines don't really change, but this can show up as either -0m00.01s or +0m00.01s, so we need to normalize the signs; additionally, some N/A's show up where we expect to get -∞ on the per-line file, and so the ∞-replacement gets the sign wrong, so we must correct it
    -e s'/[0-9]//g' # sometimes the time is under 1 minute, sometimes it's over 1 minute, so we want to remove/normalize both instances; see https://github.com/coq/coq/issues/5675#issuecomment-487378622
)

TO_SED_IN_PER_FILE=(
    -e s'/  */ /g' # unclear whether this is actually needed for per-file timing; it's been here from the start
    -e s'/\(Total.*\)-\(.*\)-/\1+\2+/g' # Overall time in the per-file timing diff should be around 0; if it comes out negative, we remove the sign
    -e s'/- ko/ko/g' # for small amounts of memory, signs can flip, so we remove mem signs
)

TO_SED_IN_PER_LINE=(
    -e s'/  */ /g' # Sometimes 0 will show up as 0m00.s, sometimes it'll end up being more like 0m00.001s; we must strip out the spaces that result from left-aligning numbers of different widths based on how many digits Coq's [-time] gives
    -e s'/^ *//g' # the number of leading spaces can differ, e.g., as in the difference between ' 0m13.53s' vs '0m13.582s'
    )
