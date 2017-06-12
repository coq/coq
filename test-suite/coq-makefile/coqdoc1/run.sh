#!/usr/bin/env bash

#set -x
set -e

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
make install-doc DSTROOT="$PWD/tmp"
#make debug
(for d in `find tmp -name user-contrib`; do pushd $d >/dev/null; find .; popd >/dev/null; done) | sort -u > actual
sort -u > desired <<EOT
.
./test
./test/test_plugin.cmi
./test/test_plugin.cmx
./test/test_plugin.cmxs
./test/test.glob
./test/test.v
./test/test.vo
./test/sub
./test/sub/testsub.glob
./test/sub/testsub.v
./test/sub/testsub.vo
./test/mlihtml
./test/mlihtml/index_exceptions.html
./test/mlihtml/index.html
./test/mlihtml/index_class_types.html
./test/mlihtml/type_Test_aux.html
./test/mlihtml/index_module_types.html
./test/mlihtml/index_classes.html
./test/mlihtml/type_Test.html
./test/mlihtml/style.css
./test/mlihtml/index_attributes.html
./test/mlihtml/index_types.html
./test/mlihtml/Test_aux.html
./test/mlihtml/index_values.html
./test/mlihtml/Test.html
./test/mlihtml/index_extensions.html
./test/mlihtml/index_methods.html
./test/mlihtml/index_modules.html
./test/html
./test/html/index.html
./test/html/test.sub.testsub.html
./test/html/toc.html
./test/html/coqdoc.css
./test/html/test.test.html
EOT
exec diff -u desired actual
