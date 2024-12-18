#!/usr/bin/env bash

if ! command -v ocamlopt; then
    echo "Skipped: no ocamlopt"
    exit 0
fi

. ../template/init.sh

# Shoud override the _CoqProject flag "-native-compiler no"
export COQEXTRAFLAGS="-native-compiler yes"

rocq makefile -f _CoqProject -o Makefile

if ! grep -q COQMF_COQ_NATIVE_COMPILER_DEFAULT=yes Makefile.conf; then
    echo "Skipped: native compile disabled or ondemand"
    exit 0
fi

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
./test/test.v
./test/test.vo
./test/.coq-native
./test/.coq-native/Ntest_test.cmi
./test/.coq-native/Ntest_test.cmx
./test/.coq-native/Ntest_test.cmxs
EOT
diff -u desired actual

(cd "$(find tmp -name coq-test-suite)" && find .) | sort > actual
sort > desired <<EOT
.
./META
./test_plugin.cmi
./test_plugin.cmx
./test_plugin.cmxa
./test_plugin.cmxs
EOT
diff -u desired actual
