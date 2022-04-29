#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download flocq3

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/flocq3"
  if ! [ -x ./configure ]; then
      autoconf
      ./configure COQEXTRAFLAGS="-compat 8.13";
  fi
  ./remake "-j${NJOBS}"
  ./remake install install-glob
)
