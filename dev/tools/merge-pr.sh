#!/usr/bin/env bash

set -e

# This script depends (at least) on git and jq.
# It should be used like this: dev/tools/merge-pr.sh /PR number/

#TODO: check arguments and show usage if relevant

PR=$1

CURRENT_LOCAL_BRANCH=`git rev-parse --abbrev-ref HEAD`
REMOTE=`git config --get branch.$CURRENT_LOCAL_BRANCH.remote`
git fetch $REMOTE refs/pull/$PR/head

API=https://api.github.com/repos/coq/coq

BASE_BRANCH=`curl -s $API/pulls/$PR | jq -r '.base.label'`

COMMIT=`git rev-parse FETCH_HEAD`
STATUS=`curl -s $API/commits/$COMMIT/status | jq -r '.state'`

if [ $BASE_BRANCH != "coq:$CURRENT_LOCAL_BRANCH" ]; then
  echo "Wrong base branch"
  read -p "Bypass? [y/N] " -n 1 -r
  echo
  if [[ ! $REPLY =~ ^[Yy]$ ]]
  then
    exit 1
  fi
fi;

if [ $STATUS != "success" ]; then
  echo "CI status is \"$STATUS\""
  read -p "Bypass? [y/N] " -n 1 -r
  echo
  if [[ ! $REPLY =~ ^[Yy]$ ]]
  then
    exit 1
  fi
fi;

git merge -S --no-ff FETCH_HEAD -m "Merge PR #$PR: `curl -s $API/pulls/$PR | jq -r '.title'`" -e

# TODO: improve this check
if [[ `git diff $REMOTE/$CURRENT_LOCAL_BRANCH dev/ci` ]]; then
  echo "******************************************"
  echo "** WARNING: does this PR have overlays? **"
  echo "******************************************"
fi
