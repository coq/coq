#!/usr/bin/env bash

. ../template/init.sh

rocq makefile -f _CoqProject -o Makefile
cat Makefile.conf
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
make install-doc DSTROOT="$PWD/tmp"
make uninstall DSTROOT="$PWD/tmp"
make uninstall-doc DSTROOT="$PWD/tmp"
#make debug
(
  while IFS= read -r -d '' d
  do
    pushd "$d" >/dev/null && find . && popd >/dev/null
  done < <(find tmp \( -name user-contrib -o -name coq-test-suite \) -print0)
) | sort -u > actual
sort -u > desired <<EOT
.
./test
./test/sub
EOT
(coqc -config | grep -q "NATIVE_COMPILER_DEFAULT=yes") || sed -i.bak '/test/d' desired
exec diff -u desired actual
