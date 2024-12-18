#!/usr/bin/env bash

. ../timing-template/init.sh

cd before/
rocq makefile -f _CoqProject -o Makefile
make cleanall
make all TIMING=before -j2 || exit $?

cd ../after/
rocq makefile -f _CoqProject -o Makefile
make cleanall
make all TIMING=after -j2 || exit $?

find ../before/ -name "*.before-timing" -exec 'cp' '{}' './' ';'
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
