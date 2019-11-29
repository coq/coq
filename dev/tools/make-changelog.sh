#!/bin/sh

echo "PR number"
read -r PR

echo "Category? (type a prefix)"
(cd doc/changelog && ls -d */)
read -r where

where="doc/changelog/$where"
if ! [ -d "$where" ]; then where=$(echo "$where"*); fi
where="$where/$PR-$(git rev-parse --abbrev-ref HEAD).rst"

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

# shellcheck disable=SC2016
# the ` are regular strings, this is intended
# use %s for the leading - to avoid looking like an option (not sure
# if necessary but doesn't hurt)
printf '%s **%s:**\n  Bla bla\n  (`#%s <https://github.com/coq/coq/pull/%s>`_,\n  by %s).' - "$type_full" "$PR" "$PR" "$(git config user.name)" > "$where"

giteditor=$(git config core.editor)
if [ "$giteditor" ]; then
    $giteditor "$where"
elif [ "$EDITOR" ]; then
    $EDITOR "$where"
else echo "$where"
fi
