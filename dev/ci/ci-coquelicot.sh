#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download coquelicot

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/coquelicot"
  if ! [ -x ./configure ]; then
      autoreconf -i -s
      ./configure
  fi
  ./remake "-j${NJOBS}"
  ./remake install
)
