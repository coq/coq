#!/bin/sh

if [ $# != 1 ]; then
    echo "Usage: $0 BRANCH"
    exit
fi

branch=$1

git checkout $branch
git pull
changelog_entries_with_title=$(ls doc/changelog/*/*.rst)
changelog_entries_no_title=$(echo "$changelog_entries_with_title" | grep -v "00000-title.rst")
git checkout master
git pull
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
