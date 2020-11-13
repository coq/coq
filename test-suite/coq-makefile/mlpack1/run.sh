#!/usr/bin/env bash

. ../template/init.sh

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
./test/.coq-native
./test/.coq-native/Ntest_test.cmi
./test/.coq-native/Ntest_test.cmx
./test/.coq-native/Ntest_test.cmxs
./test/test.glob
./test/test_plugin.cmi
./test/test_plugin.cmx
./test/test_plugin.cmxa
./test/test_plugin.cmxs
./test/test.v
./test/test.vo
EOT
(coqc -config | grep -q "NATIVE_COMPILER_DEFAULT=yes") || sed -i.bak '/\.coq-native/d' desired
exec diff -u desired actual
