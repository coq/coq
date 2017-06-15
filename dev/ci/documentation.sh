#!/usr/bin/env bash

set -ex

source dev/ci/exports.sh

get-artifact-coq-with-fallback

./configure -prefix "$CI_INSTALL" ${EXTRA_CONF}
cp "$CI_INSTALL/lib/coq/tools/coqdoc/coqdoc.sty" .

LIB="$CI_INSTALL/lib/coq"
# WTF using a newline makes make sigsev
# see https://gitlab.com/SkySkimmer/coq/builds/17313312
DOCVFILES=$(find "$LIB/" -name '*.v' -printf "%p ")
DOCLIGHTDIRS="$LIB/theories/Init/ $LIB/theories/Logic/ $LIB/theories/Unicode/ $LIB/theories/Arith/"
DOCLIGHTVOFILES=$(find $DOCLIGHTDIRS -name '*.vo' -printf "%p ")

make doc QUICK=true COQDOC_NOBOOT=true COQTEX="$CI_INSTALL/bin/coq-tex" COQDOC="$CI_INSTALL/bin/coqdoc" VFILES="$DOCVFILES" THEORIESLIGHTVO="$DOCLIGHTVOFILES"

make install-doc
