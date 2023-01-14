#!/bin/sh
# Check that both coqdep and coqtop/coqc support -R
# Check that both coqdep and coqtop/coqc take the latter -R
# See bugs #11631, #14539
rm -f deps/test-from/A/C.vo deps/test-from/B/C.vo deps/test-from/D.vo deps/test-from/E.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
coqdep -R deps/test-from T deps/test-from/D.v deps/test-from/E.v > "$tmpoutput" 2>&1
diff -u --strip-trailing-cr deps/deps-from.out "$tmpoutput"
R=$?
times
coqc -R deps/test-from T deps/test-from/A/C.v
coqc -R deps/test-from T deps/test-from/B/C.v
coqc -R deps/test-from T deps/test-from/D.v
coqc -R deps/test-from T deps/test-from/E.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
