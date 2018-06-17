#!/usr/bin/env bash

set -e
set -o pipefail

API=https://api.github.com/repos/coq/coq
OFFICIAL_REMOTE_GIT_URL="git@github.com:coq/coq"
OFFICIAL_REMOTE_HTTPS_URL="github.com/coq/coq"

# This script depends (at least) on git (>= 2.7) and jq.
# It should be used like this: dev/tools/merge-pr.sh /PR number/

# Set SLOW_CONF to have the confirmation output wait for a newline
# E.g. call $ SLOW_CONF= dev/tools/merge-pr.sh /PR number/
if [ -z ${SLOW_CONF+x} ]; then
    QUICK_CONF="-n 1"
else
    QUICK_CONF=""
fi

RED="\033[31m"
RESET="\033[0m"
GREEN="\033[32m"
BLUE="\033[34m"
YELLOW="\033[33m"
info() {
  echo -e "${GREEN}info:${RESET} $1 ${RESET}"
}
error() {
  echo -e "${RED}error:${RESET} $1 ${RESET}"
}
warning() {
  echo -e "${YELLOW}warning:${RESET} $1 ${RESET}"
}

check_util() {
if ! command -v "$1" > /dev/null 2>&1; then
  error "this script requires the $1 command line utility"
  exit 1
fi
}

ask_confirmation() {
  read -p "Continue anyway? [y/N] " $QUICK_CONF -r
  echo
  if [[ ! $REPLY =~ ^[Yy]$ ]]
  then
    exit 1
  fi
}

check_util jq
check_util curl
check_util git
check_util gpg

# command line parsing

if [ $# != 1 ]; then
  error "usage: $0 PR-number"
  exit 1
fi

if [[ "$1" =~ ^[1-9][0-9]*$ ]]; then
  PR=$1
else
  error "$1 is not a number"
  exit 1
fi

# Fetching PR metadata

PRDATA=$(curl -s "$API/pulls/$PR")

TITLE=$(echo "$PRDATA" | jq -r '.title')
info "title for PR $PR is ${BLUE}$TITLE"

BASE_BRANCH=$(echo "$PRDATA" | jq -r '.base.label')
info "PR $PR targets branch ${BLUE}$BASE_BRANCH"

CURRENT_LOCAL_BRANCH=$(git rev-parse --abbrev-ref HEAD)
info "you are merging in ${BLUE}$CURRENT_LOCAL_BRANCH"

REMOTE=$(git config --get "branch.$CURRENT_LOCAL_BRANCH.remote")
if [ -z "$REMOTE" ]; then
  error "branch ${BLUE}$CURRENT_LOCAL_BRANCH${RESET} has not associated remote"
  error "don't know where to fetch the PR from"
  error "please run: git branch --set-upstream-to=THE_REMOTE/$CURRENT_LOCAL_BRANCH"
  exit 1
fi
REMOTE_URL=$(git remote get-url "$REMOTE" --all)
if [ "$REMOTE_URL" != "${OFFICIAL_REMOTE_GIT_URL}" ] && \
   [ "$REMOTE_URL" != "${OFFICIAL_REMOTE_GIT_URL}.git" ] && \
   [ "$REMOTE_URL" != "https://${OFFICIAL_REMOTE_HTTPS_URL}" ] && \
   [ "$REMOTE_URL" != "https://${OFFICIAL_REMOTE_HTTPS_URL}.git" ] && \
   [[ "$REMOTE_URL" != "https://"*"@${OFFICIAL_REMOTE_HTTPS_URL}" ]] && \
   [[ "$REMOTE_URL" != "https://"*"@${OFFICIAL_REMOTE_HTTPS_URL}.git" ]] ; then
  error "remote ${BLUE}$REMOTE${RESET} does not point to the official Coq repo"
  error "that is ${BLUE}$OFFICIAL_REMOTE_GIT_URL"
  error "it points to ${BLUE}$REMOTE_URL${RESET} instead"
  ask_confirmation
fi
info "remote for $CURRENT_LOCAL_BRANCH is ${BLUE}$REMOTE"

info "fetching from $REMOTE the PR"
git remote update "$REMOTE"
if ! git ls-remote "$REMOTE" | grep pull >/dev/null; then
  error "remote $REMOTE is not configured to fetch pull requests"
  error "run: git config remote.$REMOTE.fetch +refs/pull/*/head:refs/remotes/$REMOTE/pr/*"
  exit 1
fi
git fetch "$REMOTE" "refs/pull/$PR/head"
COMMIT=$(git rev-parse FETCH_HEAD)
info "commit for PR $PR is ${BLUE}$COMMIT"

# Sanity check: merge to a different branch

if [ "$BASE_BRANCH" != "coq:$CURRENT_LOCAL_BRANCH" ]; then
  error "PR requests merge in ${BLUE}$BASE_BRANCH${RESET} but you are merging in ${BLUE}$CURRENT_LOCAL_BRANCH"
  ask_confirmation
fi;

# Sanity check: the local branch is up-to-date with upstream

LOCAL_BRANCH_COMMIT=$(git rev-parse HEAD)
UPSTREAM_COMMIT=$(git rev-parse @{u})
if [ "$LOCAL_BRANCH_COMMIT" != "$UPSTREAM_COMMIT" ]; then

    # Is it just that the upstream branch is behind?
    # It could just be that we merged other PRs and we didn't push yet

    if git merge-base --is-ancestor -- "$UPSTREAM_COMMIT" "$LOCAL_BRANCH_COMMIT"; then
        warning "Your branch is ahead of ${REMOTE}."
        warning "You should see this warning only if you've just merged another PR and did not push yet."
        ask_confirmation
    else
        error "Local branch is not up-to-date with ${REMOTE}."
        error "Pull before merging."
        ask_confirmation
    fi
fi

# Sanity check: PR has an outdated version of CI

BASE_COMMIT=$(echo "$PRDATA" | jq -r '.base.sha')
CI_FILES=(".travis.yml" ".gitlab-ci.yml" "appveyor.yml")

if ! git diff --quiet "$BASE_COMMIT" "$LOCAL_BRANCH_COMMIT" -- "${CI_FILES[@]}"
then
    warning "This PR didn't run with the latest version of CI."
    warning "It is probably a good idea to ask for a rebase."
    read -p "Do you want to see the diff? [Y/n] " $QUICK_CONF -r
    echo
    if [[ ! $REPLY =~ ^[Nn]$ ]]
    then
        git diff "$BASE_COMMIT" "$LOCAL_BRANCH_COMMIT" -- "${CI_FILES[@]}"
    fi
    ask_confirmation
fi

# Sanity check: CI failed

STATUS=$(curl -s "$API/commits/$COMMIT/status")

if [ "$(echo "$STATUS" | jq -r '.state')" != "success" ]; then
  error "CI unsuccessful on ${BLUE}$(echo "$STATUS" |
    jq -r -c '.statuses|map(select(.state != "success"))|map(.context)')"
  ask_confirmation
fi;

# Sanity check: has labels named "needs:"

NEEDS_LABELS=$(echo "$PRDATA" | jq -rc '.labels | map(select(.name | match("needs:"))) | map(.name)')
if [ "$NEEDS_LABELS" != "[]" ]; then
  error "needs:something labels still present: ${BLUE}$NEEDS_LABELS"
  ask_confirmation
fi

# Sanity check: has milestone

MILESTONE=$(echo "$PRDATA" | jq -rc '.milestone.title')
if [ "$MILESTONE" = "null" ]; then
  error "no milestone set, please set one"
  ask_confirmation
fi

# Sanity check: has kind

KIND=$(echo "$PRDATA" | jq -rc '.labels | map(select(.name | match("kind:"))) | map(.name)')
if [ "$KIND" = "[]" ]; then
  error "no kind:something label set, please set one"
  ask_confirmation
fi

# Sanity check: user.signingkey
if [ -z "$(git config user.signingkey)" ]; then
  warning "git config user.signingkey is empty"
  warning "gpg will guess a key out of your git config user.* data"
fi

info "merging"
git merge -v -S --no-ff FETCH_HEAD -m "Merge PR #$PR: $TITLE" -e

# TODO: improve this check
if ! git diff --quiet "$REMOTE/$CURRENT_LOCAL_BRANCH" -- dev/ci/user-overlays; then
  warning "this PR may have overlays (sorry the check is not perfect)"
  warning "if it has overlays please check the following:"
  warning "- each overlay has a corresponding open PR on the upstream repo"
  warning "- after merging please notify the upstream they can merge the PR"
fi
