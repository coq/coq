#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download compcert

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

# CompCert does compile with -native-compiler yes
# but with excessive memory requirements
export COQCOPTS='-native-compiler no -w -undeclared-scope -w -omega-is-deprecated'
(
	cd "${CI_BUILD_DIR}/compcert"
	if ! [ -e Makefile.config ]; then
		./configure -ignore-coq-version x86_32-linux -install-coqdev \
		-clightgen -use-external-MenhirLib -use-external-Flocq \
		-prefix "$COQBIN" \
		-coqdevdir "$COQLIB"/user-contrib/compcert
	fi
	make
	make check-proof COQCHK='"$(COQBIN)coqchk" -silent -o $(COQINCLUDES)'
	make install
)
