#!/bin/sh

printf "PR number? "
read -r PR

printf "Category? (type a prefix)\n"
(cd doc/changelog && ls -d */)
read -r where

where="doc/changelog/$where"
if ! [ -d "$where" ]; then where=$(echo "$where"*); fi
where="$where/$PR-$(git rev-parse --abbrev-ref HEAD | tr / -).rst"

printf "Type? (type first letter)\n"
printf "[A]dded \t[C]hanged \t[D]eprecated \t[F]ixed \t[R]emoved\n"
read -r type_first_letter

case "$type_first_letter" in
  [Aa]) type_full="Added";;
  [Cc]) type_full="Changed";;
  [Dd]) type_full="Deprecated";;
  [Ff]) type_full="Fixed";;
  [Rr]) type_full="Removed";;
  *) printf "Invalid input!\n"
     exit 1;;
esac

printf "Fixes? (space separated list of bug numbers)\n"
read -r fixes_list

fixes_string="$(echo $fixes_list | sed 's/ /~  and /g; s,\([0-9][0-9]*\),`#\1 <https://github.com/coq/coq/issues/\1>`_,g' | tr '~' '\n')"
if [ ! -z "$fixes_string" ]; then fixes_string="$(printf '\n  fixes %s,' "$fixes_string")"; fi

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option (not sure
# if necessary but doesn't hurt)
printf '%s **%s:**\n  Describe your change here but do not end with a period\n  (`#%s <https://github.com/coq/coq/pull/%s>`_,%s\n  by %s).\n' - "$type_full" "$PR" "$PR" "$fixes_string" "$(git config user.name)" > "$where"

printf 'Name of created changelog file:\n'
printf '%s\n' "$where"

giteditor=$(git config core.editor)
if [ "$giteditor" ]; then
    $giteditor "$where"
elif [ "$EDITOR" ]; then
    $EDITOR "$where"
else
    printf "Describe the changes in the above file\n"
fi
