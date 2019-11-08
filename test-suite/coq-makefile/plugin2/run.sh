#!/usr/bin/env bash

. ../template/init.sh

mv src/test_plugin.mlpack src/test_plugin.mllib
coq_makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
#make debug
(cd "$(find tmp -name user-contrib)" && find .) | sort > actual
sort > desired <<EOT
.
./test
./test/test.glob
./test/test.cmi
./test/test.cmx
./test/test_aux.cmi
./test/test_aux.cmx
./test/test_plugin.cmxa
./test/test_plugin.cmxs
./test/test.v
./test/test.vo
EOT
exec diff -u desired actual
