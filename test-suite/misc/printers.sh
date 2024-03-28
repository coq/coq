#!/bin/sh

command -v "${BIN}coqtop.byte" || { echo "Missing coqtop.byte"; exit 1; }

f=$(mktemp)
{
    printf 'Drop.\n#go;;\nQuit.\n' | "${BIN}coqtop.byte" -q
} 2>&1 | tee "$f"

# if there's an issue in `include_utilities`, `#go;;` won't be mentioned
# if there's an issue in `include_printers`, it will be an undefined printer
if ! grep -q -F '#go;;' "$f" ||
        grep -q -E -i 'Error|Unbound|Anomaly' "$f";
then exit 1; fi
