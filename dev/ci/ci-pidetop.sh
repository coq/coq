#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download pidetop

# Travis / Gitlab have different filesystem layout due to use of
# `-local`. We need to improve this divergence but if we use Dune this
# "local" oddity goes away automatically so not bothering...
if [ -d "$COQBIN/../lib/coq" ]; then
   COQLIB="$COQBIN/../lib/coq/"
else
   COQLIB="$COQBIN/../"
fi

( cd "${CI_BUILD_DIR}/pidetop" && jbuilder build @install )

echo -en '4\nexit' | "${CI_BUILD_DIR}/pidetop/_build/install/default/bin/pidetop" -coqlib "$COQLIB" -main-channel stdfds
