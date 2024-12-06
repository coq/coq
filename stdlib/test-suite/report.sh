#!/usr/bin/env bash

# save failed logs to logs/, then print failure information
# returns failure code if any failed logs exist

# save step

SAVEDIR="logs"

# reset for local builds
rm -rf "$SAVEDIR"
mkdir "$SAVEDIR"

FAILED=$(mktemp)
grep -F 'Error!' -r . -l --null --include="*.log" > "$FAILED"

rsync -a --from0 --files-from="$FAILED" . "$SAVEDIR"
cp summary.log "$SAVEDIR"/

# cleanup
rm "$FAILED"

# print info
if [ -n "$CI" ] || [ -n "$PRINT_LOGS" ]; then
    find logs/ -name '*.log' -not -name 'summary.log' -print0 | while IFS= read -r -d '' file; do
        printf '%s\n' "$file"
        cat "$file"
        printf '\n'
    done
    printed_logs=1
fi

if grep -q -F 'Error!' summary.log ; then
    echo FAILURES;
    grep -F 'Error!' summary.log;
    if [ -z "$printed_logs" ]; then
        echo 'To print details of failed tests, rerun with environment variable PRINT_LOGS=1'
        echo 'eg "make report PRINT_LOGS=1" from the test suite directory"'
        echo 'See README.md in the test suite directory for more information.'
    fi
    false
else echo NO FAILURES;
fi
