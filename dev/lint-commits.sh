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

# git diff --check
# uses .gitattributes to know what to check 
if git diff --check --ignore-space-at-eol "$BASE_COMMIT" "$HEAD_COMMIT";
then
    :
else
    >&2 echo "Whitespace errors!"
    >&2 echo "Running 'git diff --check $BASE_COMMIT $HEAD_COMMIT'."
    >&2 echo "If you use emacs, you can prevent this kind of error from reocurring by installing ws-butler and enabling ws-butler-convert-leading-tabs-or-spaces."
    exit 1
fi
