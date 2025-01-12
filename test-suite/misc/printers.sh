#!/bin/sh

f=$(mktemp)
{
    printf 'Drop.\n#go;;\nQuit.\n' | "${BIN}rocq" repl-with-drop -q
} 2>&1 | grep -a -v "Welcome to Rocq" | tee "$f"

# if there's an issue in `include_utilities`, `#go;;` won't be mentioned
# if there's an issue in `include_printers`, it will be an undefined printer
if ! grep -q -F '#go;;' "$f" ||
        grep -q -E -i 'Error|Unbound|Anomaly' "$f";
then exit 1; fi
