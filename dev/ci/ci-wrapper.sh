#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -eo pipefail

function travis_fold {
    if [ -n "${TRAVIS}" ];
    then
	echo "travis_fold:$1:$2"
    fi
}

CI_NAME="$1"
CI_SCRIPT="ci-${CI_NAME}.sh"

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Coq directory
cd "${DIR}/../.."

export TIMED=1
"${DIR}/${CI_SCRIPT}" 2>&1 | tee time-of-build.log
travis_fold 'start' 'coq.test.timing' && echo 'Aggregating timing log...'
python ./tools/make-one-time-file.py time-of-build.log
travis_fold 'end' 'coq.test.timing'
