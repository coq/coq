#!/bin/sh
# Check that coqtop/coqc and coqdep behave the same in the presence of ambiguity
# over child and sibling directories
# Same test as deps-order-subdir2-file.sh but without Subtheory2/Subsubtheory?
# so that it checks what comes first between siblings and (non immediate) children

# This test is platform-dependent, we renounce to it
dotest=true
if [ $dotest = false ]; then exit 0; fi
rm -f deps/Theory3/*.vo deps/Theory3/Subtheory?/*.vo deps/Theory3/Subtheory?/Subsubtheory?/*.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
(cd deps; coqdep -f _CoqTheory3Project) > "$tmpoutput" 2>&1
diff -u --strip-trailing-cr deps/Theory3Deps.out $tmpoutput
R=$?
if [ $R != 0 ]; then
    printf "Unexpected coqdep result.\n"
    exit 1
fi
times
coqc -Q deps/Theory3 Theory deps/Theory3/Subtheory1/File1.v
coqc -Q deps/Theory3 Theory deps/Theory3/Subtheory1/Subsubtheory2/File1.v
coqc -Q deps/Theory3 Theory deps/Theory3/Subtheory1/Subsubtheory2/File1.v
coqc -Q deps/Theory3 Theory deps/Theory3/Subtheory2/File1.v
coqc -Q deps/Theory3 Theory deps/Theory3/File2.v
S=$?
if [ $S = 0 ]; then
    printf "Unexpected coqc success.\n"
    exit 1
fi
printf "coqdep and coqc ok.\n"
