#!/usr/bin/env bash

# A script to check prettyness for a range of commits

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

BASE_COMMIT="$1"
HEAD_COMMIT="$2"

bad_ws=()
bad_compile=()
while IFS= read -r commit; do
    echo Checking "$commit"
    # git diff --check
    # uses .gitattributes to know what to check
    if ! git diff --check "${commit}^" "$commit";
    then bad_ws+=("$commit")
    fi

    if ! make -f Makefile.dune check
    then bad_compile+=("$commit")
    fi
done < <(git rev-list "$HEAD_COMMIT" --not "$BASE_COMMIT" --)

# report errors

CODE=0

if [ "${#bad_ws[@]}" != 0 ]
then
    >&2 echo "Whitespace errors!"
    >&2 echo "In commits ${bad_ws[*]}"
    >&2 echo "If you use emacs, you can prevent this kind of error from reoccurring by installing ws-butler and enabling ws-butler-convert-leading-tabs-or-spaces."
    >&2 echo
    CODE=1
fi

if [ "${#bad_compile[@]}" != 0 ]
then
    >&2 echo "Compilation errors!"
    >&2 echo "In commits ${bad_compile[*]}"
    >&2 echo
    CODE=1
fi

exit $CODE
