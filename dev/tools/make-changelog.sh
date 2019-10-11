#!/bin/sh

echo "PR number"
read -r PR

echo "Where? (type a prefix)"
(cd doc/changelog && ls -d */)
read -r where

where=$(echo doc/changelog/"$where"*)
where="$where/$PR-$(git rev-parse --abbrev-ref HEAD).rst"

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option (not sure
# if necessary but doesn't hurt)
printf '%s bla bla (`#%s <https://github.com/coq/coq/pull/%s>`_, by %s).' - "$PR" "$PR" "$(git config user.name)" > "$where"

giteditor=$(git config core.editor)
if [ "$giteditor" ]; then
    $giteditor "$where"
elif [ "$EDITOR" ]; then
    $EDITOR "$where"
else echo "$where"
fi
