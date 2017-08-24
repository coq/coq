#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -eo pipefail

function travis_fold {
    if [ -n "${TRAVIS}" ];
    then
	echo -n "travis_fold:$1:$2\\r"
    fi
}

CI_SCRIPT="$1"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Coq directory
cd "${DIR}/../.."

"${DIR}/${CI_SCRIPT}" 2>&1 | tee time-of-build.log
echo 'Aggregating timing log...' && travis_fold 'start' 'coq.test.timing'
python ./tools/make-one-time-file.py time-of-build.log
travis_fold 'end' 'coq.test.timing'
