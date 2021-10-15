#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coq_tools

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

jason_msg() {
    echo "The build broke, if an overlay is needed, mention @JasonGross in describing the expected change in Coq that needs to be taken into account, and he'll prepare a fix for coq-tools"
    exit $1
}

( cd "${CI_BUILD_DIR}/coq_tools"
  make check || jason_msg $?
)
