#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -o pipefail

CI_NAME="$1"
CI_SCRIPT="ci-${CI_NAME}.sh"

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Coq directory
cd "${DIR}/../.." || exit 1

export TIMED=1
export COQEXTRAFLAGS='-color yes'
bash "${DIR}/${CI_SCRIPT}" 2>&1 | tee time-of-build.log
code=$?
echo 'Aggregating timing log...'
python ./tools/make-one-time-file.py time-of-build.log
exit $code
