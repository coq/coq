#!/bin/sh

printf "PR number? "
read -r PR

printf "Where? (type a prefix)\n"
(cd doc/changelog && ls -d */)
read -r where

where="doc/changelog/$where"
if ! [ -d "$where" ]; then where=$(echo "$where"*); fi
where="$where/$PR-$(git rev-parse --abbrev-ref HEAD).rst"

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option (not sure
# if necessary but doesn't hurt)
printf '%s bla bla (`#%s <https://github.com/coq/coq/pull/%s>`_, by %s).' - "$PR" "$PR" "$(git config user.name)" > "$where"

printf "Name of created changelog file:\n"
printf "$where\n"

giteditor=$(git config core.editor)
if [ "$giteditor" ]; then
    $giteditor "$where"
elif [ "$EDITOR" ]; then
    $EDITOR "$where"
else
    printf "Describe the changes in the above file\n"
fi
