#!/usr/bin/env bash

# Usage: check-eof-newline.sh [--fix] FILES...
# Detect missing end of file newlines for FILES.
# Files are skipped if untracked by git and depending on gitattributes.
# With --fix, automatically append a newline.
# Exit status:
# Without --fix: 1 if any file had a missing newline, 0 otherwise.
# With --fix: 1 if any non writable file had a missing newline, 0 otherwise.

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
            if [ -w "$f" ];
            then
                echo >> "$f"
                echo "Newline appended to file $f!"
            else
                echo "File $f is missing a newline and not writable!"
                CODE=1
            fi
        else
            echo "No newline at end of file $f!"
            CODE=1
        fi
    fi
done

exit "$CODE"
