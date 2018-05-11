#!/usr/bin/env bash

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
