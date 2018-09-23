#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download plugin_tutorial

( cd "${CI_BUILD_DIR}/plugin_tutorial" && \
  pushd tuto0 && make && popd          && \
  pushd tuto1 && make && popd          && \
  pushd tuto2 && make && popd          && \
  pushd tuto3 && make && popd          )
