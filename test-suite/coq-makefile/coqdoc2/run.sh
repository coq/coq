#!/usr/bin/env bash

. ../template/init.sh

rocq makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
make install-doc DSTROOT="$PWD/tmp"
#make debug
(
  while IFS= read -r -d '' d
  do
    pushd "$d" >/dev/null && find . && popd >/dev/null
  done < <(find tmp -name user-contrib -print0)
) | sort -u > actual

sort -u > desired <<EOT
.
./test
./test/.coq-native
./test/.coq-native/Ntest_test.cmi
./test/.coq-native/Ntest_test.cmx
./test/.coq-native/Ntest_test.cmxs
./test/test.glob
./test/test.v
./test/test.vo
./test/sub
./test/sub/.coq-native
./test/sub/.coq-native/Ntest_sub_testsub.cmi
./test/sub/.coq-native/Ntest_sub_testsub.cmx
./test/sub/.coq-native/Ntest_sub_testsub.cmxs
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
(coqc -config | grep -q "NATIVE_COMPILER_DEFAULT=yes") || sed -i.bak '/\.coq-native/d' desired
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
