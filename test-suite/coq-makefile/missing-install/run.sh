#!/usr/bin/env bash

. ../template/init.sh

rm -rf _test; mkdir _test; cd _test

cat > _CoqProject <<EOF
-R theories Test
theories/a.v
theories/b.v
EOF
mkdir theories
touch theories/a.v theories/b.v

rocq makefile -f _CoqProject -o Makefile
make theories/b.vo
if make install; then exit 1; fi
