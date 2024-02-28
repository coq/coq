#!/usr/bin/env bash

. ../timing-template/init.sh

cd before/
coq_makefile -f _CoqProject -o Makefile
make cleanall
make make-pretty-timed-before TGTS="all" -j1 || exit $?

cd ../after/

coq_makefile -f _CoqProject -o Makefile
make cleanall

make make-pretty-timed-after TGTS="all" -j1 || exit $?
rm -f time-of-build-before.log

make print-pretty-timed-diff TIMING_SORT_BY=diff TIME_OF_BUILD_BEFORE_FILE=../before/time-of-build-before.log
cp ../before/time-of-build-before.log ./

make print-pretty-timed-diff TIMING_SORT_BY=diff || exit $?

for file in time-of-build-before.log time-of-build-after.log time-of-build-both.log; do
  for ext in "" .desired; do
    sed "${TO_SED_IN_BOTH[@]}" "${TO_SED_IN_PER_FILE[@]}" ${file}${ext} > ${file}${ext}.processed
  done
  echo "cat $file"
  cat "$file"
  echo
  diff -u $file.desired.processed $file.processed || exit $?
done
