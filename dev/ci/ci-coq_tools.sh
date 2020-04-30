#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_tools

( cd "${CI_BUILD_DIR}/coq_tools" && make check || \
  { RV=$?; echo "The build broke, if an overlay is needed, mention @JasonGross in describing the expected change in Coq that needs to be taken into account, and he'll prepare a fix for coq-tools"; exit $RV; } )
