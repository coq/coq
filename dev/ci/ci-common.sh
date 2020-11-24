#!/usr/bin/env bash

set -xe

# default value for NJOBS
: "${NJOBS:=1}"
export NJOBS

if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build, Coq installed into `_install_ci`
    export OCAMLPATH="$PWD/_install_ci/lib:$OCAMLPATH"
    export COQBIN="$PWD/_install_ci/bin"
    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$PWD/_build/install/default/" ];
then
    # Dune build
    export OCAMLPATH="$PWD/_build/install/default/lib/:$PWD/_install_ci/lib:$OCAMLPATH"
    export COQBIN="$PWD/_build/install/default/bin"
    export COQLIB="$PWD/_build/install/default/lib/coq"
    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
else
    # We assume we are in `-profile devel` build, thus `-local` is set
    export OCAMLPATH="$PWD:$PWD/_install_ci/lib:$OCAMLPATH"
    export COQBIN="$PWD/bin"
    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
fi

export PATH="$COQBIN:$PWD/_install_ci/bin:$PATH"

# Coq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"

ls -l "$COQBIN"

# Where we download and build external developments
CI_BUILD_DIR="$PWD/_build_ci"

# Where we install external binaries and ocaml libraries
CI_INSTALL_DIR="$PWD/_install_ci"

ls -l "$CI_BUILD_DIR" || true

declare -A overlays

overlay()
{
    local project=$1
    local ov_url=$2
    local ov_ref=$3

    overlays[${project}_URL]=$ov_url
    overlays[${project}_REF]=$ov_ref
}

set +x
for overlay in "${ci_dir}"/user-overlays/*.sh; do
    # shellcheck source=/dev/null
    . "${overlay}"
done

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
  local project=$1
  local dest="$CI_BUILD_DIR/$project"

  local giturl_var="${project}_CI_GITURL"
  local giturl="${!giturl_var}"
  local ref_var="${project}_CI_REF"
  local ref="${!ref_var}"

  local ov_url=${overlays[${project}_URL]}
  local ov_ref=${overlays[${project}_REF]}

  if [ -d "$dest" ]; then
    echo "Warning: download and unpacking of $project skipped because $dest already exists."
  elif [[ $ov_url ]] || [ "$FORCE_GIT" = "1" ] || [ "$CI" = "" ]; then
    git clone "$giturl" "$dest"
    cd "$dest"
    git checkout "$ref"
    git log -n 1
    if [[ $ov_url ]]; then
        git -c pull.rebase=false -c user.email=nobody@example.invalid -c user.name=Nobody \
            pull --no-ff "$ov_url" "$ov_ref"
        git log -n 1 HEAD^2
        git log -n 1
    fi
  else # When possible, we download tarballs to reduce bandwidth and latency
    local archiveurl_var="${project}_CI_ARCHIVEURL"
    local archiveurl="${!archiveurl_var}"
    mkdir -p "$dest"
    cd "$dest"
    local commit
    commit=$(git ls-remote "$giturl" "refs/heads/$ref" | cut -f 1)
    if [[ "$commit" == "" ]]; then
      # $ref must have been a tag or hash, not a branch
      commit="$ref"
    fi
    wget "$archiveurl/$commit.tar.gz"
    tar xfz "$commit.tar.gz" --strip-components=1
    rm -f "$commit.tar.gz"
  fi
}

make()
{
    # +x: add x only if defined
    if [ -z "${MAKEFLAGS+x}" ] && [ -n "${NJOBS}" ];
    then
        # Not submake and parallel make requested
        command make --output-sync -j "$NJOBS" "$@"
    else
        command make --output-sync "$@"
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
