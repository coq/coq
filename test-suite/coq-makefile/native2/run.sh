#!/usr/bin/env bash

if ! command -v ocamlopt; then
    echo "Skipped: no ocamlopt"
    exit 0
fi

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile

if ! grep -q COQMF_COQ_NATIVE_COMPILER_DEFAULT=yes Makefile.conf; then
    echo "Skipped: native compile disabled or ondemand"
    exit 0
fi

cat Makefile.conf
COQEXTRAFLAGS="-w +native-compiler-disabled -native-compiler yes" make
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
