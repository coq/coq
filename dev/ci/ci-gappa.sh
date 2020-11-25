 #!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download gappa_tool

( cd "${CI_BUILD_DIR}/gappa_tool" && ( if [ ! -x ./configure ]; then autoreconf && touch stamp-config_h.in && ./configure --prefix=${CI_INSTALL_DIR}; fi ) && ./remake "-j${NJOBS}" && ./remake install )

git_download gappa_plugin

( cd "${CI_BUILD_DIR}/gappa_plugin" && ( if [ ! -x ./configure ]; then autoconf && ./configure; fi ) && ./remake "-j${NJOBS}" && ./remake install )
