#!/usr/bin/env bash

# TODO:
#
# - Check if the branch already exists in the remote => checkout
# - Better error handling
# - Just checkout, don't build
# - Rebase functionality
#

set -x
set -e
set -o pipefail

# setup_contrib_git("_build_ci/fiat", "https://github.com/ejgallego/fiat-core.git")
setup_contrib_git() {

    local _DIR=$1
    local _GITURL=$2

    ( cd $_DIR
      git checkout -b $OVERLAY_BRANCH         || true # allow the branch to exist already
      git remote add $DEVELOPER_NAME $_GITURL || true # allow the remote to exist already
    )

}

if [ $# -lt 3 ]; then
  echo "usage: $0 github_username pr_number contrib1 ... contribN"
  exit 1
fi

set +x
. dev/ci/ci-basic-overlay.sh
set -x

DEVELOPER_NAME=$1
shift
PR_NUMBER=$1
shift
OVERLAY_BRANCH=$(git rev-parse --abbrev-ref HEAD)
OVERLAY_FILE=$(mktemp overlay-XXXX)

# Create the overlay file
> "$OVERLAY_FILE"

# We first try to build the contribs
while test $# -gt 0
do
    _CONTRIB_NAME=$1
    _CONTRIB_GITURL=${_CONTRIB_NAME}_CI_GITURL
    _CONTRIB_GITURL=${!_CONTRIB_GITURL}
    echo "Processing Contrib $_CONTRIB_NAME"

    # check _CONTRIB_GIT exists and it is of the from github...

    _CONTRIB_DIR=_build_ci/$_CONTRIB_NAME

    # extract the relevant part of the repository
    _CONTRIB_GITSUFFIX=${_CONTRIB_GITURL#https://github.com/*/}
    _CONTRIB_GITURL="https://github.com/$DEVELOPER_NAME/$_CONTRIB_GITSUFFIX"
    _CONTRIB_GITPUSHURL="git@github.com:$DEVELOPER_NAME/${_CONTRIB_GITSUFFIX}.git"

    DOWNLOAD_ONLY=1 make ci-$_CONTRIB_NAME || true
    setup_contrib_git $_CONTRIB_DIR $_CONTRIB_GITPUSHURL

    echo "overlay ${_CONTRIB_NAME} $_CONTRIB_GITURL $OVERLAY_BRANCH $PR_NUMBER" >> $OVERLAY_FILE
    shift
done

# Copy to overlays folder.
PR_NUMBER=$(printf '%05d' "$PR_NUMBER")
mv $OVERLAY_FILE dev/ci/user-overlays/$PR_NUMBER-$DEVELOPER_NAME-${OVERLAY_BRANCH///}.sh
