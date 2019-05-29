#!/bin/sh

command -v "${BIN}coqtop.byte" || { echo "Missing coqtop.byte"; exit 1; }

f=$(mktemp)
printf 'Drop. #use"include";; #quit;;\n' | "${BIN}coqtop.byte" -q 2>&1 | tee "$f"

if grep -q -E "Error|Unbound" "$f"; then exit 1; fi
