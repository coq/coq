#!/usr/bin/env bash

# A script to check prettyness for a range of commits
set -e

CALLNAME="$0"

function usage
{
    >&2 echo "usage: $CALLNAME <commit> <commit>"
    >&2 echo "The order of commits is as given to 'git diff'"
}

if [ "$#" != 2 ];
then
    usage
    exit 1
fi

REDBOLD="\033[31;1m"
RESET="\033[0m"

function redprint
{
  if true || [ "$COQ_CI_COLOR" ]; then
    printf "$REDBOLD%s$RESET\n" "$1"
  else
    printf '%s\n' "$1"
  fi
}

BASE_COMMIT="$1"
HEAD_COMMIT="$2"

tmp=$(mktemp -d)
git worktree add "$tmp" "$HEAD_COMMIT"
pushd "$tmp"

bad_ws=()
bad_compile=()
while IFS= read -r commit; do
    echo Checking "$commit"
    git checkout "$commit"

    # git diff --check
    # uses .gitattributes to know what to check
    if ! git diff --check "${commit}^" "$commit";
    then bad_ws+=("$commit")
    fi

    if ! make check
    then bad_compile+=("$commit")
    fi
done < <(git rev-list "$HEAD_COMMIT" --not "$BASE_COMMIT" --)

popd
git worktree remove "$tmp"

# report errors

CODE=0

if [ "${#bad_ws[@]}" != 0 ]
then
    >&2 redprint "Whitespace errors!"
    >&2 echo "In commits ${bad_ws[*]}"
    >&2 echo "If you use emacs, you can prevent this kind of error from reoccurring by installing ws-butler and enabling ws-butler-convert-leading-tabs-or-spaces."
    >&2 echo
    CODE=1
fi

if [ "${#bad_compile[@]}" != 0 ]
then
    >&2 redprint "Compilation errors!"
    >&2 echo "In commits ${bad_compile[*]}"
    >&2 echo
    CODE=1
fi

exit $CODE
