#!/usr/bin/env bash

CODE=0
for f in "$@"; do
    if git ls-files --error-unmatch "$f" >/dev/null 2>&1 && \
           git check-attr whitespace -- "$f" | grep -q -v -e 'unset$' -e 'unspecified$' && \
           [ -n "$(tail -c 1 "$f")" ]
    then
        echo "No newline at end of file $f!"
        CODE=1
    fi
done

exit "$CODE"
