#!/bin/sh
# Check that both coqdep and coqtop/coqc support -R
# Check that both coqdep and coqtop/coqc take the latter -R
# See bugs #11631, #14539
rm -f misc/deps/test-from/A/C.vo misc/deps/test-from/B/C.vo misc/deps/test-from/D.vo misc/deps/test-from/E.vo
output=misc/deps/deps-from.real
$coqdep -worker @ROCQWORKER@ -R misc/deps/test-from T misc/deps/test-from/D.v misc/deps/test-from/E.v > "$output" 2>&1
diff -u --strip-trailing-cr misc/deps/deps-from.out "$output"
R=$?
times
$coqc -R misc/deps/test-from T misc/deps/test-from/A/C.v
$coqc -R misc/deps/test-from T misc/deps/test-from/B/C.v
$coqc -R misc/deps/test-from T misc/deps/test-from/D.v
$coqc -R misc/deps/test-from T misc/deps/test-from/E.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
