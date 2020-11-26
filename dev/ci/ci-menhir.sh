ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download menhirlib

( cd "${CI_BUILD_DIR}/menhirlib" && dune build @install -p menhirLib,menhirSdk,menhir && dune install -p menhirLib,menhirSdk,menhir menhir menhirSdk menhirLib --prefix=${CI_INSTALL_DIR} )

( cd "${CI_BUILD_DIR}/menhirlib" && make -C coq-menhirlib && make -C coq-menhirlib install )
