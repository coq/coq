#!/usr/bin/env bash

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi

if [ "${BASH_SOURCE[0]}" ]; then
  root="$(dirname "${BASH_SOURCE[0]}")/../.."
  # make path absolute if relative
  root=$(cd "$root" > /dev/null && echo "$PWD")
elif [ -e "$PWD/dev/ci/ci-env.sh" ]; then
  root=$PWD
else
  >&2 echo "BASH_SOURCE not working (too old bash version?)"
  >&2 echo "update bash or run this script from the rocq repository's root directory"
  exit 1
fi

echo "Root is" $root
# We can remove setting ROCQLIB and ROCQRUNTIMELIB from here, but better to
# wait until we have merged the coq.boot patch so we can do this in a
# more controlled way.
if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build, Rocq installed into `_install_ci`
    export COQBIN="$root/_install_ci/bin"
    export OCAMLPATH="$root/_install_ci/lib$OCAMLFINDSEP$OCAMLPATH"
    export PATH="$root/_install_ci/bin:$PATH"

    # Where we install external binaries and ocaml libraries
    # also generally used for dune install --prefix so needs to match coq's expected user-contrib path
    CI_INSTALL_DIR="$root/_install_ci"

    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$root/_build/install/default/" ];
then
    # Full Dune build, we basically do what `dune exec --` does
    export OCAMLPATH="$root/_build/install/default/lib/$OCAMLFINDSEP$OCAMLPATH"
    export COQBIN="$root/_build/install/default/bin"
    export ROCQLIB="$root/_build/install/default/lib/coq"
    export ROCQRUNTIMELIB="$root/_build/install/default/lib/rocq-runtime"

    CI_INSTALL_DIR="$root/_build/install/default/"

    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
fi

export PATH="$COQBIN:$PATH"

# Rocq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"
