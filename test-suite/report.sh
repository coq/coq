#!/usr/bin/env bash

# save failed logs to logs/, then print failure information
# returns failure code if any failed logs exist

# save step

SAVEDIR="logs"

# reset for local builds
rm -rf "$SAVEDIR"
mkdir "$SAVEDIR"

# keep this synced with test-suite/Makefile
FAILMARK="==========> FAILURE <=========="

FAILED=$(mktemp /tmp/coq-check-XXXXXX)
find . '(' -path ./bugs/opened -prune ')' -o '(' -name '*.log' -exec grep "$FAILMARK" -q '{}' ';' -print0 ')' > "$FAILED"

rsync -a --from0 --files-from="$FAILED" . "$SAVEDIR"
cp summary.log "$SAVEDIR"/

# cleanup
rm "$FAILED"

# print info
if [ -n "$TRAVIS" ] || [ -n "$PRINT_LOGS" ]; then
    find logs/ -name '*.log' -not -name 'summary.log' -print0 | while IFS= read -r -d '' file; do
        if [ -n "$TRAVIS" ]; then
            # ${foo////.} replaces every / by . in $foo
            printf 'travis_fold:start:coq.logs.%s\n' "${file////.}";
        else printf '%s\n' "$file"
        fi

        cat "$file"

        if [ -n "$TRAVIS" ]; then
            # ${foo////.} replaces every / by . in $foo
            printf 'travis_fold:end:coq.logs.%s\n' "${file////.}";
        else printf '\n'
        fi
    done
fi

if grep -q -F 'Error!' summary.log ; then
    echo FAILURES;
    grep -F 'Error!' summary.log;
    if [ -z "$TRAVIS" ] && [ -z "$PRINT_LOGS" ]; then
        echo 'To print details of failed tests, rerun with environment variable PRINT_LOGS=1'
        echo 'eg "make report PRINT_LOGS=1" from the test suite directory"'
        echo 'See README.md in the test suite directory for more information.'
    fi
    false
else echo NO FAILURES;
fi
