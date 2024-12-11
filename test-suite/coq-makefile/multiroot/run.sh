#!/usr/bin/env bash

. ../template/init.sh

cp -r theories theories2
mv src/test_plugin.mlpack src/test_plugin.mllib
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
./test2
./test2/.coq-native
./test2/.coq-native/Ntest2_test.cmi
./test2/.coq-native/Ntest2_test.cmx
./test2/.coq-native/Ntest2_test.cmxs
./test2/test.glob
./test2/test.v
./test2/test.vo
./orphan_test_test2_test
./orphan_test_test2_test/html
./orphan_test_test2_test/html/coqdoc.css
./orphan_test_test2_test/html/index.html
./orphan_test_test2_test/html/test2.test.html
./orphan_test_test2_test/html/test.test.html
./orphan_test_test2_test/html/toc.html
./orphan_test_test2_test/mlihtml
./orphan_test_test2_test/mlihtml/index_attributes.html
./orphan_test_test2_test/mlihtml/index_classes.html
./orphan_test_test2_test/mlihtml/index_class_types.html
./orphan_test_test2_test/mlihtml/index_exceptions.html
./orphan_test_test2_test/mlihtml/index_extensions.html
./orphan_test_test2_test/mlihtml/index.html
./orphan_test_test2_test/mlihtml/index_methods.html
./orphan_test_test2_test/mlihtml/index_modules.html
./orphan_test_test2_test/mlihtml/index_module_types.html
./orphan_test_test2_test/mlihtml/index_types.html
./orphan_test_test2_test/mlihtml/index_values.html
./orphan_test_test2_test/mlihtml/style.css
./orphan_test_test2_test/mlihtml/Test_aux.html
./orphan_test_test2_test/mlihtml/Test.html
./orphan_test_test2_test/mlihtml/type_Test_aux.html
./orphan_test_test2_test/mlihtml/type_Test.html
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
