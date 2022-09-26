#!/bin/sh
# Check reading directories matching non pure ascii idents
# See bug #5715 (utf-8 working on macos X and linux)
# Windows is still not compliant
a=$(uname)
if [ "$a" = "Darwin" ] || [ "$a" = "Linux" ]; then
rm -f deps/théorèmes/*.v
tmpoutput=$(mktemp /tmp/coqcheck.XXXXXX)
coqc -R deps AlphaBêta deps/αβ/γδ.v
R=$?
coqc -R deps AlphaBêta deps/αβ/εζ.v
S=$?
if [ $R = 0 ] && [ $S = 0 ]; then
    exit 0
else
    exit 1
fi
fi
