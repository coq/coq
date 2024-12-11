#!/usr/bin/env bash

. ../template/init.sh

cat > _CoqProject <<EOF
-R ./theories/ ""
theories/b.v
theories/a.v
theories/noSuchFile.v
EOF
touch theories/a.v
cat > theories/b.v <<EOF
Require a.
EOF

rocq makefile -f _CoqProject -o Makefile

if make 2> stdErr.log; then exit 1; fi

# on osx it says "No rule to make target `.Makefile.d', needed by `theories/b.vo'.  Stop."
#grep -q noSuchFile stdErr.log
