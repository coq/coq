#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -eo pipefail

CI_SCRIPT="$1"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Coq directory
cd "${DIR}/../.."

"${DIR}/${CI_SCRIPT}" 2>&1 | tee time-of-build.log
echo 'Aggregating timing log...' && echo -en 'travis_fold:start:coq.test.timing\\r'
python ./tools/make-one-time-file.py time-of-build.log
echo -en 'travis_fold:end:coq.test.timing\\r'
