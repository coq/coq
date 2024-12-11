#!/bin/sh
# Check that both coqdep and coqtop/coqc supports -R
# Check that both coqdep and coqtop/coqc takes the later -R
# See bugs 2242, 2337, 2339
rm -f misc/deps/lib/*.vo misc/deps/client/*.vo
output=misc/deps/deps.real

$coqdep -worker @COQWORKER@ -R misc/deps/lib lib -R misc/deps/client client misc/deps/client/bar.v 2>&1 | head -n 1 > "$output"
diff -u --strip-trailing-cr misc/deps/deps.out "$output" 2>&1
R=$?
times
$coqc -R misc/deps/lib lib misc/deps/lib/foo.v 2>&1
$coqc -R misc/deps/lib lib -R misc/deps/client client misc/deps/client/foo.v 2>&1
$coqc -R misc/deps/lib lib -R misc/deps/client client misc/deps/client/bar.v 2>&1
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree\n"
    exit 0
else
    printf "coqdep and coqc disagree\n"
    exit 1
fi
