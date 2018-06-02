#!/usr/bin/env bash

set -xe

# default value for NJOBS
: "${NJOBS:=1}"
export NJOBS

if [ -n "${GITLAB_CI}" ];
then
    export OCAMLPATH="$PWD/_install_ci/lib:$OCAMLPATH"
    export COQBIN="$PWD/_install_ci/bin"
    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
else
    if [ -n "${TRAVIS}" ];
    then
        export CI_PULL_REQUEST="$TRAVIS_PULL_REQUEST"
        export CI_BRANCH="$TRAVIS_BRANCH"
    elif [ -n "${CIRCLECI}" ];
    then
        export CI_PULL_REQUEST="$CIRCLE_PR_NUMBER"
        export CI_BRANCH="$CIRCLE_BRANCH"
    else # assume local
        CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
        export CI_BRANCH
    fi
    export OCAMLPATH="$PWD:$OCAMLPATH"
    export COQBIN="$PWD/bin"
fi
export PATH="$COQBIN:$PATH"

# Coq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"

ls "$COQBIN"

# Where we clone and build external developments
CI_BUILD_DIR="$PWD/_build_ci"

# shellcheck source=ci-basic-overlay.sh
. "${ci_dir}/ci-basic-overlay.sh"
for overlay in "${ci_dir}"/user-overlays/*.sh; do
    # shellcheck source=/dev/null
    . "${overlay}"
done

mathcomp_CI_DIR="${CI_BUILD_DIR}/math-comp"

# git_checkout branch url dest will create a git repository
# in <dest> (if it does not exist already) and checkout the
# remote branch <branch> from <url>
git_checkout()
{
  local _BRANCH=${1}
  local _URL=${2}
  local _DEST=${3}

  # Allow an optional 4th argument for the commit
  local _COMMIT=${4:-FETCH_HEAD}
  local _DEPTH=()
  if [ -z "${4}" ]; then _DEPTH=(--depth 1); fi

  mkdir -p "${_DEST}"
  ( cd "${_DEST}"                                                     && \
    if [ ! -d .git ] ; then git clone "${_DEPTH[@]}" "${_URL}" . ; fi && \
    echo "Checking out ${_DEST}"                                      && \
    git fetch "${_URL}" "${_BRANCH}"                                  && \
    git checkout "${_COMMIT}"                                         && \
    echo "${_DEST}: $(git log -1 --format='%s | %H | %cd | %aN')" )
}

make()
{
    # +x: add x only if defined
    if [ -z "${MAKEFLAGS+x}" ] && [ -n "${NJOBS}" ];
    then
        # Not submake and parallel make requested
        command make -j "$NJOBS" "$@"
    else
        command make "$@"
    fi
}

# this installs just the ssreflect library of math-comp
install_ssreflect()
{
  echo 'Installing ssreflect' && echo -en 'travis_fold:start:ssr.install\\r'

  git_checkout "${mathcomp_CI_BRANCH}" "${mathcomp_CI_GITURL}" "${mathcomp_CI_DIR}"

  ( cd "${mathcomp_CI_DIR}/mathcomp" && \
    sed -i.bak '/ssrtest/d'     Make && \
    sed -i.bak '/odd_order/d'   Make && \
    sed -i.bak '/all\/all.v/d'  Make && \
    sed -i.bak '/character/d'   Make && \
    sed -i.bak '/real_closed/d' Make && \
    sed -i.bak '/solvable/d'    Make && \
    sed -i.bak '/field/d'       Make && \
    sed -i.bak '/fingroup/d'    Make && \
    sed -i.bak '/algebra/d'     Make && \
    make Makefile.coq && make -f Makefile.coq all && make install )

  echo -en 'travis_fold:end:ssr.install\\r'

}
