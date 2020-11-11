#!/bin/sh
# Check that both coqdep and coqtop/coqc support -R
# Check that both coqdep and coqtop/coqc take the latter -R
# See also bugs #2242, #2337, #2339
rm -f deps/DistinctRoot/*.vo deps/DistinctRoot/*.vo/{A,B}/*.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
(cd deps; coqdep -f _CoqDistinctRoot) > "$tmpoutput" 2>&1
diff -u --strip-trailing-cr deps/DistinctRootDeps.out "$tmpoutput"
R=$?
times
coqc -R deps/DistinctRoot/A A -R deps/DistinctRoot/B B deps/DistinctRoot/A/File1.v
coqc -R deps/DistinctRoot/A A -R deps/DistinctRoot/B B deps/DistinctRoot/B/File1.v
coqc -R deps/DistinctRoot/A A -R deps/DistinctRoot/B B deps/DistinctRoot/File2.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree.\n"
    exit 0
else
    printf "coqdep and coqc disagree.\n"
    exit 1
fi
