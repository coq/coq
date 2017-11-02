#!/usr/bin/env bash

# This file should be called from the top-level directory of Coq!
export LC_ALL=C
COMPILE_DATE=`date`

# default coq version
COQ_VERSION=`cat COQ_VERSION || echo "unknown"`

echo "type version = { describe : string; branch : string; hash : string } ;;"

if [ -x `which git` ] && [ -d .git ]
then
    GIT_DESCRIBE=`git describe --tags --first-parent --dirty | sed 's/^V//'`
    GIT_BRANCH=`git branch -a | sed -ne '/^\* /s/^\* \(.*\)/\1/p'`
    GIT_HASH=`git rev-parse HEAD`
    echo "let version = { describe = \"${GIT_DESCRIBE}\"; branch = \"${GIT_BRANCH}\"; hash = \"${GIT_HASH}\" } ;;"
else
    echo "let version = { describe = \"${COQ_VERSION}\"; branch = \"unknown\"; hash = \"\" } ;;"
fi

echo "let compile_date = \"${COMPILE_DATE}\" ;;"
