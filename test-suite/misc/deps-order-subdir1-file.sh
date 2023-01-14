#!/bin/sh
# Check that both coqdep and coqtop/coqc takes a file matching exactly
# the logical path (if any)
rm -f deps/Theory1/*.vo deps/Theory1/Subtheory?/*.vo deps/Theory1/Subtheory?/Subsubtheory?/*.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
(cd deps; coqdep -f _CoqTheory1Project) > "$tmpoutput" 2>&1
diff -u --strip-trailing-cr deps/Theory1Deps.out "$tmpoutput"
R=$?
times
coqc -Q deps/Theory1 Theory deps/Theory1/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory1/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory1/Subsubtheory1/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory1/Subsubtheory2/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory2/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory2/Subsubtheory1/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/Subtheory2/Subsubtheory2/File1.v
coqc -Q deps/Theory1 Theory deps/Theory1/File2.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree.\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
