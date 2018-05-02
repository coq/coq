#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

pidetop_CI_DIR="${CI_BUILD_DIR}/pidetop"

git_checkout "${pidetop_CI_BRANCH}" "${pidetop_CI_GITURL}" "${pidetop_CI_DIR}"

( cd "${pidetop_CI_DIR}" && coq_makefile -f Make -o Makefile.top && make -f Makefile.top "-j${NJOBS}" && make install-toploop -f Makefile.top )

echo -en '4\nexit' | coqtop -main-channel stdfds -toploop pidetop
