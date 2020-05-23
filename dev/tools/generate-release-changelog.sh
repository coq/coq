#!/usr/bin/env bash

set -e
set -o pipefail

if [ $# != 1 ]; then
    echo "Usage: $0 BRANCH"
    exit
fi

branch=$1

# Set SLOW_CONF to have the confirmation output wait for a newline
# Emacs doesn't send characters until the RET so we can't quick_conf
if [ -z ${SLOW_CONF+x} ] || [ -n "$INSIDE_EMACS" ]; then
    quick_conf="-n 1"
else
    quick_conf=""
fi

ask_confirmation() {
    read -p "Continue anyway? [y/N] " $quick_conf -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 1
    fi
}

if ! git diff --quiet; then
    echo "Warning: current tree is dirty."
    ask_confirmation
fi

remote=$(git config --get "branch.${branch}.remote" || true)

if [ -z "$remote" ]; then
    echo "Warning: branch $branch has no associated remote."
    ask_confirmation
else

    if [ "$remote" != $(git config --get "branch.master.remote" || true) ]; then
        echo "Warning: branch master and branch $branch do not have the same remote."
        ask_confirmation
    fi

    official_remote_git_url="git@github.com:coq/coq"
    official_remote_https_url="github.com/coq/coq"
    remote_url=$(git remote get-url "$remote" --all)

    if [ "$remote_url" != "${official_remote_git_url}" ] && \
           [ "$remote_url" != "${official_remote_git_url}.git" ] && \
           [ "$remote_url" != "https://${official_remote_https_url}" ] && \
           [ "$remote_url" != "https://${official_remote_https_url}.git" ] && \
           [[ "$remote_url" != "https://"*"@${official_remote_https_url}" ]] && \
           [[ "$remote_url" != "https://"*"@${official_remote_https_url}.git" ]] ; then
        echo "Warning: remote $remote does not point to the official Coq repo,"
        echo "that is $official_remote_git_url"
        echo "It points to $remote_url instead."
        ask_confirmation
    fi

    git fetch "$remote"

    if [ $(git rev-parse master) != $(git rev-parse "${remote}/master") ]; then
        echo "Warning: branch master is not up-to-date with ${remote}/master."
        ask_confirmation
    fi

    if [ $(git rev-parse "$branch") != $(git rev-parse "${remote}/${branch}") ]; then
        echo "Warning: branch ${branch} is not up-to-date with ${remote}/${branch}."
        ask_confirmation
    fi

fi

git checkout $branch --detach
changelog_entries_with_title=$(ls doc/changelog/*/*.rst)
changelog_entries_no_title=$(echo "$changelog_entries_with_title" | grep -v "00000-title.rst")
git checkout master
for f in $changelog_entries_with_title; do
    if [ -f "$f" ]; then
        cat "$f" >> released.rst
    else
        echo "Warning: $f is missing in master branch."
    fi
done
for f in $changelog_entries_no_title; do
    if [ -f "$f" ]; then
        git rm "$f"
    fi
done
echo "Changelog written in released.rst. Move its content to a new section in doc/sphinx/changes.rst."
