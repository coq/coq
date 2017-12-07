#!/usr/bin/env bash

# Usage: dev/tools/backport-pr.sh <PR number>

set -e

PRNUM=$1

if ! git log master --grep "Merge PR #${PRNUM}" | grep "." > /dev/null; then
    echo "PR #${PRNUM} does not exist."
    exit 1
fi

SIGNATURE_STATUS=$(git log master --grep "Merge PR #${PRNUM}" --format="%G?")
git log master --grep "Merge PR #${PRNUM}" --format="%GG"
if [[ "${SIGNATURE_STATUS}" != "G" ]]; then
    echo
    read -p "Merge commit does not have a good (valid) signature. Bypass? [y/N] " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
fi

BRANCH=backport-pr-${PRNUM}
RANGE=$(git log master --grep "Merge PR #${PRNUM}" --format="%P" | sed 's/ /../')
MESSAGE=$(git log master --grep "Merge PR #${PRNUM}" --format="%s" | sed 's/Merge/Backport/')

if git checkout -b ${BRANCH}; then

    if ! git cherry-pick -x ${RANGE}; then
        echo "Please fix the conflicts, then exit."
        bash
        while ! git cherry-pick --continue; do
            echo "Please fix the conflicts, then exit."
            bash
        done
    fi
    git checkout -

else

    echo
    read -p "Skip directly to merging phase? [y/N] " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi

fi

git merge -S --no-ff ${BRANCH} -m "${MESSAGE}"
git branch -d ${BRANCH}

# To-Do:
# - Support for backporting a PR before it is merged
# - Automatically backport all PRs in the "Waiting to be backported" column using a command like:
# $ curl -s -H "Authorization: token ${GITHUB_TOKEN}" -H "Accept: application/vnd.github.inertia-preview+json" https://api.github.com/projects/columns/1358120/cards | jq -r '.[].content_url' | grep issue | sed 's/^.*issues\/\([0-9]*\)$/\1/' | tac
# (The ID of the column must first be obtained through https://api.github.com/repos/coq/coq/projects then https://api.github.com/projects/819866/columns.)
# - Then move each of the backported PR to the subsequent columns automatically as well...
