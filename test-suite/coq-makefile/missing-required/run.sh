#!/usr/bin/env bash

. ../template/init.sh

cat > _CoqProject <<EOF
-R ./theories/ "Lib"
theories/a.v
EOF
cat > theories/a.v <<EOF
Require noSuchFile.
EOF

rocq makefile -f _CoqProject -o Makefile

if make 2> stdErr.log; then exit 1; fi

grep -q noSuchFile stdErr.log
