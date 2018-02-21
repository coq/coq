#!/usr/bin/env bash

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
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
  done < <(find tmp -name user-contrib -print0)
) | sort -u > actual
sort -u > desired <<EOT
.
EOT
exec diff -u desired actual
