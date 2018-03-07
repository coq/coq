#!/usr/bin/env bash

# $0 is not the safest way, but...
ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

pidetop_CI_DIR="${CI_BUILD_DIR}/pidetop"

git_checkout "${pidetop_CI_BRANCH}" "${pidetop_CI_GITURL}" "${pidetop_CI_DIR}"

# Travis / Gitlab have different filesystem layout due to use of
# `-local`. We need to improve this divergence but if we use Dune this
# "local" oddity goes away automatically so not bothering...
if [ -d "$COQBIN/../lib/coq" ]; then
   COQOCAMLLIB="$COQBIN/../lib/"
   COQLIB="$COQBIN/../lib/coq/"
else
   COQOCAMLLIB="$COQBIN/../"
   COQLIB="$COQBIN/../"
fi

( cd "${pidetop_CI_DIR}" && OCAMLPATH="$COQOCAMLLIB" jbuilder build @install )

echo -en '4\nexit' | "$pidetop_CI_DIR/_build/install/default/bin/pidetop" -coqlib "$COQLIB" -main-channel stdfds
