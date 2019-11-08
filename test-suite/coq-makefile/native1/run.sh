#!/usr/bin/env bash

NATIVECOMP=$(grep "let no_native_compiler = false" ../../../config/coq_config.ml)||true
if [[ $(which ocamlopt) && $NATIVECOMP ]]; then

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
./test/test.glob
./test/test_plugin.cmi
./test/test_plugin.cmx
./test/test_plugin.cmxa
./test/test_plugin.cmxs
./test/test.v
./test/test.vo
./test/.coq-native
./test/.coq-native/Ntest_test.cmi
./test/.coq-native/Ntest_test.cmx
./test/.coq-native/Ntest_test.cmxs
EOT
exec diff -u desired actual

fi
exit 0 # test skipped
