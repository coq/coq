#!/usr/bin/env bash

. ../template/path-init.sh

set -x
coq_makefile -Q . Top foo.v -o Makefile
rm -f .*.d *.d
make --no-print-directory -j1 printvo 2>&1 \
    | grep -v 'make[^:]*: warning: -jN forced in submake: disabling jobserver mode.' \
    | grep -v 'coq_makefile -Q . Top foo.v -o Makefile' \
    | grep -v 'make[^:]*: Entering directory' \
    | grep -v 'make[^:]*: Leaving directory' \
    | grep -v 'exit 1' \
           > make-printvo.log
diff -u make-printvo.log.expected make-printvo.log || exit $?
