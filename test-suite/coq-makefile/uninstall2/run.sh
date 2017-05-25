#!/bin/bash

#set -x
set -e

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make
make html mlihtml
make install DSTROOT="$PWD/tmp"
make install-doc DSTROOT="$PWD/tmp"
make uninstall DSTROOT="$PWD/tmp"
make uninstall-doc DSTROOT="$PWD/tmp"
#make debug
(for d in `find tmp -name user-contrib`; do pushd $d >/dev/null; find; popd >/dev/null; done) | sort -u > actual
sort -u > desired <<EOT
.
EOT
exec diff -u desired actual
