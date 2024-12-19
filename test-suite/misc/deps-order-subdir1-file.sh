#!/bin/sh
# Check that both coqdep and coqtop/coqc takes a file matching exactly
# the logical path (if any)
rm -f misc/deps/Theory1/*.vo misc/deps/Theory1/Subtheory?/*.vo misc/deps/Theory1/Subtheory?/Subsubtheory?/*.vo
output=misc/deps/Theory1Deps.real
(cd misc/deps; $coqdep -worker @ROCQWORKER@ -f _CoqTheory1Project) > "$output" 2>&1
diff -u --strip-trailing-cr misc/deps/Theory1Deps.out "$output"
R=$?
times
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory1/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory1/Subsubtheory1/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory1/Subsubtheory2/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory2/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory2/Subsubtheory1/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/Subtheory2/Subsubtheory2/File1.v
$coqc -Q misc/deps/Theory1 Theory misc/deps/Theory1/File2.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree.\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
