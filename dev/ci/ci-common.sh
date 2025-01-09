#!/usr/bin/env bash

set -xe

# default value for NJOBS
: "${NJOBS:=1}"
export NJOBS

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi

# We can remove setting ROCQLIB and ROCQRUNTIMELIB from here, but better to
# wait until we have merged the coq.boot patch so we can do this in a
# more controlled way.
if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build, Coq installed into `_install_ci`
    export COQBIN="$PWD/_install_ci/bin"
    export OCAMLPATH="$PWD/_install_ci/lib$OCAMLFINDSEP$OCAMLPATH"
    export PATH="$PWD/_install_ci/bin:$PATH"

    # Where we install external binaries and ocaml libraries
    # also generally used for dune install --prefix so needs to match coq's expected user-contrib path
    CI_INSTALL_DIR="$PWD/_install_ci"

    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$PWD/_build/install/default/" ];
then
    # Full Dune build, we basically do what `dune exec --` does
    export OCAMLPATH="$PWD/_build/install/default/lib/$OCAMLFINDSEP$OCAMLPATH"
    export COQBIN="$PWD/_build/install/default/bin"
    export ROCQLIB="$PWD/_build/install/default/lib/coq"
    export ROCQRUNTIMELIB="$PWD/_build/install/default/lib/rocq-runtime"

    CI_INSTALL_DIR="$PWD/_build/install/default/"

    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
fi

export PATH="$COQBIN:$PATH"

# Coq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"

ls -l "$COQBIN"

# Where we download and build external developments
CI_BUILD_DIR="$PWD/_build_ci"

ls -l "$CI_BUILD_DIR" || true

declare -A overlays

# overlay <project> <giturl> <ref> <prnumber> [<prbranch>]
#   creates an overlay for project using a given url and branch which is
#   active for prnumber or prbranch. prbranch defaults to ref.
function overlay()
{
    local project=$1
    local ov_url=$2
    local ov_ref=$3
    local ov_prnumber=$4
    local ov_prbranch=$5
    : "${ov_prbranch:=$ov_ref}"

    if [ "$CI_PULL_REQUEST" = "$ov_prnumber" ] || [ "$CI_BRANCH" = "$ov_prbranch" ]; then
      if ! is_in_projects "$project"; then
        echo "Error: $1 is not a known project which can be overlayed"
        exit 1
      fi

      overlays[${project}_URL]=$ov_url
      overlays[${project}_REF]=$ov_ref
    fi
}

set +x
# shellcheck source=ci-basic-overlay.sh
. "${ci_dir}/ci-basic-overlay.sh"

for overlay in "${ci_dir}"/user-overlays/*.sh; do
    # shellcheck source=/dev/null
    # the directoy can be empty
    if [ -e "${overlay}" ]; then . "${overlay}"; fi
done
set -x

# [git_download <project> [<destination>]] will download <project> and
# unpack it in <destination> (if given; default:
# $CI_BUILD_DIR/<project>) if the folder does not exist already; if it
# does, it will do nothing except print a warning (this can be useful
# when building locally).
# Note: when there is an overlay, $WITH_SUBMODULES is set to 1 or $CI
# is unset or empty (local build), it uses git clone to perform the
# download.
git_download()
{
  local project=$1
  local dest="${2:-$CI_BUILD_DIR/$project}"

  local giturl_var="${project}_CI_GITURL"
  local giturl="${!giturl_var}"
  local ref_var="${project}_CI_REF"
  local ref="${!ref_var}"
  local parent_project_var="${project}_CI_PARENT_PROJECT"
  local parent_project="${!parent_project_var}"
  local submodule_folder_var="${project}_CI_SUBMODULE_FOLDER"
  local submodule_folder="${!submodule_folder_var}"

  local ov_url=${overlays[${project}_URL]}
  local ov_ref=${overlays[${project}_REF]}

  local dest_prefix="$(dirname "$dest")/"
  if [ "${CI}${USE_CI_DIRECTORY_STRUCTURE}" = "" ]; then
    # we can reuse the parent project download when not on CI
    local parent_project_dest="$CI_BUILD_DIR/$parent_project"
    # we use relative symlinks so they are relocatable
    local parent_project_relative_dest="${parent_project_dest#$dest_prefix}"
  else
    # on CI, we need to ensure that there's no overlap in directory tree
    # between sibling jobs, since otherwise they will scribble over
    # each others .v timestamps and result in duplicated builds
    local parent_project_dest="${dest}-PARENT-${parent_project}"
    # we use relative symlinks so they are relocatable
    local parent_project_relative_dest="${parent_project_dest#$dest_prefix}"
  fi

  if [ -d "$dest" ]; then
    echo "Warning: download and unpacking of $project skipped because $dest already exists."
  elif [[ $ov_url ]] || [ "$WITH_SUBMODULES" = "1" ] || [ "$CI" = "" ] || [ -n "${parent_project}" ]; then
    if [ -n "${parent_project}" ]; then
      # if there is a parent project, we first download the parent
      # project then symlink the submodule_folder to dest; this allows
      # project CI scripts to be transparent w.r.t. whether or not the
      # project is cloned from a submodule / submodule_folder.
      if [ ! -d "${parent_project_dest}" ]; then
        WITH_SUBMODULES=1 git_download "${parent_project}" "${parent_project_dest}"
      fi
      # now we can create the symlinks
      ln -s "${parent_project_relative_dest}/${submodule_folder}" "$dest"
      pushd "$dest"
      ref="$(git rev-parse HEAD)"
    else
      git clone "$giturl" "$dest"
      pushd "$dest"
      git checkout "$ref"
    fi
    git log -n 1
    if [[ $ov_url ]]; then
        # In CI we merge into the upstream branch to stay synchronized
        # Locally checkout the overlay and rebase on upstream
        # We act differently because merging is what will happen when the PR is merged
        # but rebasing produces something that is nicer to edit
        if [[ $CI ]]; then
            git -c pull.rebase=false -c user.email=nobody@example.invalid -c user.name=Nobody \
                pull --no-edit --no-ff "$ov_url" "$ov_ref"
            git log -n 1 HEAD^2 || true # no merge commit if the overlay was merged upstream
            git log -n 1
        else
            git remote add -t "$ov_ref" -f overlay "$ov_url"
            git checkout -b "$ov_ref" overlay/"$ov_ref"
            git rebase "$ref"
            git log -n 1
        fi
    fi
    if [ "$WITH_SUBMODULES" = 1 ]; then
        git submodule update --init --recursive
    fi
    popd
  else # When possible, we download tarballs to reduce bandwidth and latency
    local archiveurl_var="${project}_CI_ARCHIVEURL"
    local archiveurl="${!archiveurl_var}"
    mkdir -p "$dest"
    pushd "$dest"
    local commit
    commit=$(git ls-remote "$giturl" "refs/heads/$ref" | cut -f 1)
    if [[ "$commit" == "" ]]; then
      # $ref must have been a tag or hash, not a branch
      commit="$ref"
    fi
    wget "$archiveurl/$commit.tar.gz"
    tar xfz "$commit.tar.gz" --strip-components=1
    rm -f "$commit.tar.gz"
    popd
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

# run make -k; make again if it failed so that the failing file comes last
# makes it easier to find the error messages in the CI log
function make_full() {
    if ! make -k "$@"; then make -k "$@"; exit 1; fi
}
