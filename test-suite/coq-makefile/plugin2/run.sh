#!/usr/bin/env bash

. ../template/init.sh

mv src/test_plugin.mlpack src/test_plugin.mllib
rocq makefile -f _CoqProject -o Makefile
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
./test/test.v
./test/test.vo
EOT
(coqc -config | grep -q "NATIVE_COMPILER_DEFAULT=yes") || sed -i.bak '/\.coq-native/d' desired
diff -u desired actual

(cd "$(find tmp -name coq-test-suite)" && find .) | sort > actual
sort > desired <<EOT
.
./META
./test.cmi
./test.cmx
./test_aux.cmi
./test_aux.cmx
./test_plugin.cmxa
./test_plugin.cmxs
EOT
diff -u desired actual
