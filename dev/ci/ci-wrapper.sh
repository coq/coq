#!/usr/bin/env bash

# Use this script to preserve the exit code of $CI_SCRIPT when piping
# it to `tee time-of-build.log`.  We have a separate script, because
# this only works in bash, which we don't require project-wide.

set -o pipefail
set -x

CI_NAME="$1"
CI_SCRIPT="ci-${CI_NAME}.sh"

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
# assume this script is in dev/ci/, cd to the root Rocq directory
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

# we don't want to block commands on user interaction
export GIT_PAGER=
if [ "$COQ_CI_COLOR" = 1 ] && command -v script > /dev/null; then
  # prevent piping from disabling auto colors / enable auto colors in CI
    if [ "$CI" ]; then
      export TERM=xterm-color
    fi
    # on some macos systems OSTYPE is just "darwin", on others it's followed by version info
    if [[ "$OSTYPE" =~ ^darwin ]]; then
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

printf "\n%s exit code: %s\n" "$CI_NAME" "$code" >> "$CI_NAME.log"

# the test suite already prints a timing table
if [ "$CI_NAME" != stdlib_test ]; then
  echo 'Aggregating timing log...'
  echo
  tools/make-one-time-file.py --real "$CI_NAME.log"
fi

if [ "$CI" ] && ! [ $code = 0 ]; then
  set +x

  escape_re=$(printf '\033%s' '\[[0-9;]+m')

  # File ".*
  file_re="($escape_re)?"'File ".*\n'

  # OCaml: error message may contain some code extracts starting with the line number,
  # followed by a line containing "^^^" to point at the columns (possibly colored)
  codeline_re='([0-9].*\n)*'
  carets_re="((($escape_re)|[ ^])*\n)?"

  # Error messages may be multiline, but it's hard to find the end
  # heuristic: if the line ends with ":" or ",", also print the next
  # (typically if the start of the message got moved to the next line,
  #  the first line is just "Error:",
  #  also note that OCaml colors just "Error" but Rocq colors the whole "Error:")
  error_re="($escape_re)?Error(.*[:,]($escape_re)?\n)*.*\n"

  # for some reason when testing with colors on
  # I also got carriage returns in my output which confused grep, so remove them

  # -P: perl-like
  # -z: multiline using \0 chars (which is why we have to tr to cleanup the output)
  # -o: print only matched (otherwise it prints the whole file due to -z)

  # || true: if no error is matched by this pattern, we still want to use the error code from the build
  < "$CI_NAME.log" tr -d "$(printf '\r')" \
    | grep -Pzo "$file_re$codeline_re$carets_re$error_re" \
    | tr -d '\0' > errors \
    || true

  if [ -s errors ]; then {
    echo
    echo "Error list (may be incomplete):"
    echo
    cat errors
  } >&2
  fi
  rm errors

fi
exit $code
