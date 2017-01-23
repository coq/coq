#!/bin/sh

#set -x
set -e

if which ocamlopt; then

. ../template/init.sh
	
coq_makefile -f _CoqProject -o Makefile
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
#make debug
(cd `find tmp -name user-contrib`; find) | sort > actual
sort > desired <<EOT
.
./test
./test/test.glob
./test/test_plugin.cmi
./test/test_plugin.cmo
./test/test_plugin.cmx
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
