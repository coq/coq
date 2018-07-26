#!/usr/bin/env bash

#set -x
set -e

. ../template/path-init.sh

# reset MAKEFLAGS so that, e.g., `make -C test-suite -B coq-makefile` doesn't give us issues

MAKEFLAGS=

cd precomputed-time-tests
./run.sh || exit $?

cd ../error
coq_makefile -f _CoqProject -o Makefile
make cleanall
if make pretty-timed TGTS="all" -j1; then
    echo "Error: make pretty-timed should have failed"
    exit 1
fi

cd ../aggregate
coq_makefile -f _CoqProject -o Makefile
make cleanall
make pretty-timed TGTS="all" -j1 || exit $?

cd ../before
coq_makefile -f _CoqProject -o Makefile
make cleanall
make make-pretty-timed-before TGTS="all" -j1 || exit $?

cd ../after
coq_makefile -f _CoqProject -o Makefile
make cleanall
make make-pretty-timed-after TGTS="all" -j1 || exit $?
rm -f time-of-build-before.log
make print-pretty-timed-diff TIMING_SORT_BY=diff TIME_OF_BUILD_BEFORE_FILE=../before/time-of-build-before.log
cp ../before/time-of-build-before.log ./
make print-pretty-timed-diff TIMING_SORT_BY=diff || exit $?

INFINITY="∞"
INFINITY_REPLACEMENT="+.%" # assume that if the before time is zero, we expected the time to increase

TO_SED_IN_BOTH=(
    -e s"/${INFINITY}/${INFINITY_REPLACEMENT}/g" # Whether or not something shows up as ∞ depends on whether a time registers as 0.s or as 0.001s, so we can't rely on this being consistent
    -e s':|\s*N/A\s*$:| '"${INFINITY_REPLACEMENT}"':g' # Whether or not something shows up as N/A depends on whether a time registers as 0.s or as 0.001s, so we can't rely on this being consistent
    -e s'/ *$//g' # the number of trailing spaces depends on how many digits percentages end up being; since this varies across runs, we remove trailing spaces
    -e s'/[0-9]*\.[0-9]*//g' # the precise timing numbers vary, so we strip them out
    -e s'/^-*$/------/g' # When none of the numbers get over 100 (or 1000, in per-file), the width of the table is different, so we normalize the number of dashes for table separators
    -e s'/+/-/g' # some code lines don't really change, but this can show up as either -0m00.01s or +0m00.01s, so we need to normalize the signs; additionally, some N/A's show up where we expect to get -∞ on the per-line file, and so the ∞-replacement gets the sign wrong, so we must correct it
)

TO_SED_IN_PER_FILE=(
    -e s'/[0-9]//g' # unclear whether this is actually needed above and beyond s'/[0-9]*\.[0-9]*//g'; it's been here from the start
    -e s'/  */ /g' # unclear whether this is actually needed for per-file timing; it's been here from the start
    -e s'/\(Total.*\)-\(.*\)-/\1+\2+/g' # Overall time in the per-file timing diff should be around 0; if it comes out negative, we remove the sign
)

TO_SED_IN_PER_LINE=(
    -e s'/0//g' # unclear whether this is actually needed above and beyond s'/[0-9]*\.[0-9]*//g'; it's been here from the start
    -e s'/  */ /g' # Sometimes 0 will show up as 0m00.s, sometimes it'll end up being more like 0m00.001s; we must strip out the spaces that result from left-aligning numbers of different widths based on how many digits Coq's [-time] gives
    )

for file in time-of-build-before.log time-of-build-after.log time-of-build-both.log; do
  for ext in "" .desired; do
    grep -v 'warning: undefined variable' < ${file}${ext} | sed "${TO_SED_IN_BOTH[@]}" "${TO_SED_IN_PER_FILE[@]}" > ${file}${ext}.processed
  done
  echo "cat $file"
  cat "$file"
  echo
  diff -u $file.desired.processed $file.processed || exit $?
done

cd ../per-file-before
coq_makefile -f _CoqProject -o Makefile
make cleanall
make all TIMING=before -j2 || exit $?

cd ../per-file-after
coq_makefile -f _CoqProject -o Makefile
make cleanall
make all TIMING=after -j2 || exit $?

find ../per-file-before/ -name "*.before-timing" -exec 'cp' '{}' './' ';'
make all.timing.diff -j2 || exit $?
echo "cat A.v.before-timing"
cat A.v.before-timing
echo
echo "cat A.v.after-timing"
cat A.v.after-timing
echo
echo "cat A.v.timing.diff"
cat A.v.timing.diff
echo

file=A.v.timing.diff

for ext in "" .desired; do
    sed "${TO_SED_IN_BOTH[@]}" "${TO_SED_IN_PER_LINE[@]}" < "${file}${ext}" | sort > "${file}${ext}.processed"
done

diff -u "$file.desired.processed" "$file.processed" || exit $?

exit 0
