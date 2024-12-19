#!/bin/sh
# Check that coqtop/coqc and coqdep behave the same in the presence of ambiguity
# over child and sibling directories
# Same test as deps-order-subdir2-file.sh but without Subtheory2/Subsubtheory?
# so that it checks what comes first between siblings and (non immediate) children

# This test is platform-dependent, we renounce to it
dotest=true
if [ $dotest = false ]; then exit 0; fi
rm -f misc/deps/Theory3/*.vo misc/deps/Theory3/Subtheory?/*.vo misc/deps/Theory3/Subtheory?/Subsubtheory?/*.vo
output=misc/deps/Theory3Deps.real
(cd misc/deps; $coqdep -worker @ROCQWORKER@ -f _CoqTheory3Project) > "$output" 2>&1
diff -u --strip-trailing-cr misc/deps/Theory3Deps.out $output
R=$?
if [ $R != 0 ]; then
    printf "Unexpected coqdep result.\n"
    exit 1
fi
times
$coqc -Q misc/deps/Theory3 Theory misc/deps/Theory3/Subtheory1/File1.v
$coqc -Q misc/deps/Theory3 Theory misc/deps/Theory3/Subtheory1/Subsubtheory2/File1.v
$coqc -Q misc/deps/Theory3 Theory misc/deps/Theory3/Subtheory1/Subsubtheory2/File1.v
$coqc -Q misc/deps/Theory3 Theory misc/deps/Theory3/Subtheory2/File1.v
$coqc -Q misc/deps/Theory3 Theory misc/deps/Theory3/File2.v
S=$?
if [ $S = 0 ]; then
    printf "Unexpected coqc success.\n"
    exit 1
fi
printf "coqdep and coqc ok.\n"
