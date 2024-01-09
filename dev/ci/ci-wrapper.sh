#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -o pipefail
set -x

CI_NAME="$1"
CI_SCRIPT="ci-${CI_NAME}.sh"

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Coq directory
cd "${DIR}/../.." || exit 1

export TIMED=1

# if COQ_CI_COLOR is set (from the environment) keep it intact (even when it's the empty string)'
if ! [ "${COQ_CI_COLOR+1}" ]; then
  # NB: in CI TERM is unset in the environment
  # when TERM is unset, bash sets it to "dumb" as a bash variable (not exported?)
  if { [ -t 1 ] && ! [ "$TERM" = dumb ]; } || [ "$CI" ]
  then COQ_CI_COLOR=1
  else COQ_CI_COLOR=
  fi
fi

if [ "$COQ_CI_COLOR" = 1 ] && command -v script > /dev/null; then
  # prevent piping from disabling auto colors / enable auto colors in CI
    if [ "$CI" ]; then
      export TERM=xterm-color
      export GIT_PAGER=
    fi
    if [ "$OSTYPE" = darwin ]; then
        script -q /dev/null bash "${DIR}/${CI_SCRIPT}" 2>&1 | tee "$CI_NAME.log"
    else
        script --quiet --flush --return -c "bash '${DIR}/${CI_SCRIPT}'" /dev/null 2>&1 | tee "$CI_NAME.log"
    fi
else
  if [ "$COQ_CI_COLOR" = 1 ]; then
    >&2 echo 'script command not available, colors will be hidden'
  fi
  bash "${DIR}/${CI_SCRIPT}" 2>&1 | tee "$CI_NAME.log"
fi
code=$?
echo 'Aggregating timing log...'
python ./tools/make-one-time-file.py --real "$CI_NAME.log"
exit $code
