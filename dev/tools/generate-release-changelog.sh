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
    quick_conf=(-n 1)
else
    quick_conf=()
fi

ask_confirmation() {
    read -p "Continue anyway? [y/N] " "${quick_conf[@]}" -r
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

    if [[ "$remote" != $(git config --get "branch.master.remote") ]]; then
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

    if [[ $(git rev-parse master) != $(git rev-parse "${remote}/master") ]]; then
        echo "Warning: branch master is not up-to-date with ${remote}/master."
        ask_confirmation
    fi

    if [[ $(git rev-parse "$branch") != $(git rev-parse "${remote}/${branch}") ]]; then
        echo "Warning: branch ${branch} is not up-to-date with ${remote}/${branch}."
        ask_confirmation
    fi

fi

git checkout "$branch" --detach > /dev/null 2>&1
changelog_entries_with_title=(doc/changelog/*/*.rst)
git checkout master > /dev/null 2>&1

tmp=$(mktemp)
for f in "${changelog_entries_with_title[@]}"; do
    if ! [ -f "$f" ]; then
        >&2 echo "Warning: $f is missing in master branch."
        continue
    fi

    cat=${f%/*} # dirname
    if [[ ${f##*/} = 00000-title.rst ]]; then
        type=0
    else
        type_name=$(head -n 1 "$f" | cut -f 2 -d ' ')
        type_name=${type_name%":**"}
        type_name=${type_name#"**"}
        case "$type_name" in
            Changed) type=1;;
            Removed) type=2;;
            Deprecated) type=3;;
            Added) type=4;;
            Fixed) type=5;;
            *) >&2 echo "Unknown changelog type $type_name in $f"; type=6;;
        esac
    fi
    printf '%s %s %s\n' "$cat" "$type" "$f" >> "$tmp"
done

while read -r _ type f; do
    cat "$f" >> released.rst
    if ! [[ $type = 0 ]]; then git rm "$f" >> /dev/null; fi
done < <(sort "$tmp")

echo
echo "Changelog written in released.rst. Move its content to a new section in doc/sphinx/changes.rst."
