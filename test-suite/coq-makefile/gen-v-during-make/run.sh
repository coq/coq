#!/usr/bin/env bash

. ../template/init.sh

cat > _CoqProject <<EOF
-R ./theories/ ""
theories/use.v
theories/generatedInPreAll.v
EOF

cat > theories/use.v <<EOF
Require generatedInPreAll.
EOF

printf 'theories/generatedInPreAll.v:\n\ttouch theories/generatedInPreAll.v\n' > Makefile.local

coq_makefile -f _CoqProject -o Makefile
make
