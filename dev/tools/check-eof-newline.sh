#!/usr/bin/env bash

# Usage: check-eof-newline.sh [--fix] FILES...
# Detect missing end of file newlines for FILES.
# Files are skipped if untracked by git and depending on gitattributes.
# With --fix, automatically append a newline.
# Exit status: 1 if any file had a missing newline, 0 otherwise
# (regardless of --fix).

FIX=
if [ "$1" = --fix ];
then
   FIX=1
   shift
fi

CODE=0
for f in "$@"; do
    if git ls-files --error-unmatch "$f" >/dev/null 2>&1 && \
           git check-attr whitespace -- "$f" | grep -q -v -e 'unset$' -e 'unspecified$' && \
           [ -n "$(tail -c 1 "$f")" ]
    then
        if [ -n "$FIX" ];
        then
            echo >> "$f"
            echo "Newline appended to file $f!"
        else
            echo "No newline at end of file $f!"
        fi
        CODE=1
    fi
done

exit "$CODE"
