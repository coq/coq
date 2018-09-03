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

# Where we download and build external developments
CI_BUILD_DIR="$PWD/_build_ci"

for overlay in "${ci_dir}"/user-overlays/*.sh; do
    # shellcheck source=/dev/null
    . "${overlay}"
done
# shellcheck source=ci-basic-overlay.sh
. "${ci_dir}/ci-basic-overlay.sh"

# [git_download project] will download [project] and unpack it
# in [$CI_BUILD_DIR/project] if the folder does not exist already;
# if it does, it will do nothing except print a warning (this can be
# useful when building locally).
# Note: when $FORCE_GIT is set to 1 or when $CI is unset or empty
# (local build), it uses git clone to perform the download.
git_download()
{
  local PROJECT=$1
  local DEST="$CI_BUILD_DIR/$PROJECT"

  if [ -d "$DEST" ]; then
    echo "Warning: download and unpacking of $PROJECT skipped because $DEST already exists."
  elif [ "$FORCE_GIT" = "1" ] || [ "$CI" = "" ]; then
    local GITURL_VAR="${PROJECT}_CI_GITURL"
    local GITURL="${!GITURL_VAR}"
    local REF_VAR="${PROJECT}_CI_REF"
    local REF="${!REF_VAR}"
    git clone "$GITURL" "$DEST"
    cd "$DEST"
    git checkout "$REF"
  else # When possible, we download tarballs to reduce bandwidth and latency
    local ARCHIVEURL_VAR="${PROJECT}_CI_ARCHIVEURL"
    local ARCHIVEURL="${!ARCHIVEURL_VAR}"
    local REF_VAR="${PROJECT}_CI_REF"
    local REF="${!REF_VAR}"
    mkdir -p "$DEST"
    cd "$DEST"
    wget "$ARCHIVEURL/$REF.tar.gz"
    tar xvfz "$REF.tar.gz" --strip-components=1
    rm -f "$REF.tar.gz"
  fi
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
  echo 'Installing ssreflect'

  git_download mathcomp

  ( cd "${CI_BUILD_DIR}/mathcomp/mathcomp" && \
    make Makefile.coq && \
    make -f Makefile.coq ssreflect/all_ssreflect.vo && \
    make -f Makefile.coq install )

}

# this installs just the ssreflect + algebra library of math-comp
install_ssralg()
{
  echo 'Installing ssralg'

  git_download mathcomp

  ( cd "${CI_BUILD_DIR}/mathcomp/mathcomp" && \
    make Makefile.coq && \
    make -f Makefile.coq algebra/all_algebra.vo && \
    make -f Makefile.coq install )

}
