#!/usr/bin/env bash

set -xe

# default value for NJOBS
: "${NJOBS:=1}"
export NJOBS

if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build with Dune
    export OCAMLPATH="$PWD/_build/install/default/lib/"
    export COQBIN="$PWD/_build/install/default/bin"
    export COQLIB="$PWD/_build/install/default/lib/coq"
    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$PWD/_build/install/default/" ];
then
    # Dune build
    export OCAMLPATH="$PWD/_build/install/default/lib/"
    export COQBIN="$PWD/_build/install/default/bin"
    export COQLIB="$PWD/_build/install/default/lib/coq"
    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
else
    # We assume we are in `-profile devel` build, thus `-local` is set
    export OCAMLPATH="$PWD:$OCAMLPATH"
    export COQBIN="$PWD/bin"
    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
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

set +x
# shellcheck source=ci-basic-overlay.sh
. "${ci_dir}/ci-basic-overlay.sh"
set -x

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
  local GITURL_VAR="${PROJECT}_CI_GITURL"
  local GITURL="${!GITURL_VAR}"
  local REF_VAR="${PROJECT}_CI_REF"
  local REF="${!REF_VAR}"

  if [ -d "$DEST" ]; then
    echo "Warning: download and unpacking of $PROJECT skipped because $DEST already exists."
  elif [ "$FORCE_GIT" = "1" ] || [ "$CI" = "" ]; then
    git clone "$GITURL" "$DEST"
    cd "$DEST"
    git checkout "$REF"
  else # When possible, we download tarballs to reduce bandwidth and latency
    local ARCHIVEURL_VAR="${PROJECT}_CI_ARCHIVEURL"
    local ARCHIVEURL="${!ARCHIVEURL_VAR}"
    mkdir -p "$DEST"
    cd "$DEST"
    local COMMIT=$(git ls-remote "$GITURL" "refs/heads/$REF" | cut -f 1)
    if [[ "$COMMIT" == "" ]]; then
      # $REF must have been a tag or hash, not a branch
      COMMIT="$REF"
    fi
    wget "$ARCHIVEURL/$COMMIT.tar.gz"
    tar xvfz "$COMMIT.tar.gz" --strip-components=1
    rm -f "$COMMIT.tar.gz"
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

  ( cd "${CI_BUILD_DIR}/mathcomp/mathcomp/ssreflect" && \
    make && \
    make install )

}

# this installs just the ssreflect + algebra library of math-comp
install_ssralg()
{
  echo 'Installing ssralg'

  git_download mathcomp

  ( cd "${CI_BUILD_DIR}/mathcomp/mathcomp" && \
    make -C ssreflect && \
    make -C ssreflect install && \
    make -C fingroup && \
    make -C fingroup install && \
    make -C algebra && \
    make -C algebra install )

}
