#!/bin/sh
# Check that both coqdep and coqtop/coqc support -R
# Check that both coqdep and coqtop/coqc take the latter -R
# See also bugs #2242, #2337, #2339
rm -f misc/deps/DistinctRoot/*.vo misc/deps/DistinctRoot/*.vo/{A,B}/*.vo
output=misc/deps/DistinctRootDeps.real
(cd misc/deps; $coqdep -worker @ROCQWORKER@ -f _CoqDistinctRoot) > "$output" 2>&1
diff -u --strip-trailing-cr misc/deps/DistinctRootDeps.out "$output"
R=$?
times
$coqc -R misc/deps/DistinctRoot/A A -R misc/deps/DistinctRoot/B B misc/deps/DistinctRoot/A/File1.v
$coqc -R misc/deps/DistinctRoot/A A -R misc/deps/DistinctRoot/B B misc/deps/DistinctRoot/B/File1.v
$coqc -R misc/deps/DistinctRoot/A A -R misc/deps/DistinctRoot/B B misc/deps/DistinctRoot/File2.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree.\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
