#!/bin/sh

command -v "${BIN}coqtop.byte" || { echo "Missing coqtop.byte"; exit 1; }

f=$(mktemp)
{
    printf 'Drop.\n#directory "../dev";;\n#use "ml_toplevel/include";;\n#quit;;\n' | "${BIN}coqtop.byte" -q
} 2>&1 | tee "$f"

# if there's an issue in `include_utilities`, 'go' won't be defined
# if there's an issue in `include_printers`, it will be an undefined printer
if ! grep -q -F 'val go : unit -> unit = <fun>' "$f" ||
        grep -q -E 'Error|Unbound' "$f";
then exit 1; fi
