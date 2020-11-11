#!/bin/sh
# Check that both coqdep and coqtop/coqc supports -R
# Check that both coqdep and coqtop/coqc takes the later -R
# See bugs 2242, 2337, 2339
rm -f deps/lib/*.vo deps/client/*.vo
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
coqdep -R deps/lib lib -R deps/client client deps/client/bar.v 2>&1 | head -n 1 > "$tmpoutput"
diff -u --strip-trailing-cr deps/deps.out "$tmpoutput" 2>&1
R=$?
times
coqc -R deps/lib lib deps/lib/foo.v 2>&1
coqc -R deps/lib lib -R deps/client client deps/client/foo.v 2>&1
coqc -R deps/lib lib -R deps/client client deps/client/bar.v 2>&1
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    printf "coqdep and coqc agree\n"
    exit 0
else
    printf "coqdep and coqc disagree\n"
    exit 1
fi
