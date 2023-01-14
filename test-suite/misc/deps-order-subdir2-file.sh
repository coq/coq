#!/bin/sh
# Check that coqtop/coqc and coqdep behave the same in the presence of ambiguity
# over child and sibling directories
# Same test as deps-order-subdir1-file.sh but without Theory1/File1.v

# This test is platform-dependent, we renounce to it
dotest=true
if [ $dotest = false ]; then exit 0; fi
rm -f deps/Theory2/*.vo deps/Theory2/Subtheory?/*.vo deps/Theory2/Subtheory?/Subsubtheory?/*.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
(cd deps; coqdep -f _CoqTheory2Project) > "$tmpoutput" 2>&1
diff -u --strip-trailing-cr deps/Theory2Deps.out $tmpoutput
R=$?
if [ $R != 0 ]; then
    printf "Unexpected coqdep result.\n"
    exit 1
fi
times
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory1/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory1/Subsubtheory2/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory1/Subsubtheory2/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory2/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory2/Subsubtheory2/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/Subtheory2/Subsubtheory2/File1.v
coqc -Q deps/Theory2 Theory deps/Theory2/File2.v
S=$?
if [ $S = 0 ]; then
    printf "Unexpected coqc success.\n"
    exit 1
fi
printf "coqdep and coqc ok.\n"
