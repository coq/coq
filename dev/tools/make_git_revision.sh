#!/usr/bin/env bash

if ! command -v git >/dev/null; then
    >&2 echo "skipping make_git_revision: git not found"
    exit 0
fi

if [ -d .git ] || git rev-parse --git-dir > /dev/null 2>&1
then
    export LANG=C
    GIT_BRANCH=$(git branch -a | sed -ne '/^\* /s/^\* \(.*\)/\1/p')
    GIT_HOST=$(hostname)
    GIT_PATH=$(pwd)
    echo "${GIT_HOST}:${GIT_PATH},${GIT_BRANCH}"
    echo $(git log -1 --pretty='format:%H')
else
    >&2 echo "skipping make_git_revision: git dir not found"
    exit 0
fi
