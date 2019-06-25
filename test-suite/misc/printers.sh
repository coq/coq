#!/bin/sh

command -v "${BIN}coqtop.byte" || { echo "Missing coqtop.byte"; exit 1; }

f=$(mktemp)
{
    if [ -n "$INSIDE_DUNE" ]; then
        printf 'Drop.\n#directory "../dev";;\n#use "include_dune";;\n#quit;;\n' | coqtop.byte -q
    else
        # -I ../dev is not needed when compiled with -local (usual dev
        # setup), but is needed for CI testing.
        printf 'Drop. #use "include";; #quit;;\n' | "${BIN}coqtop.byte" -I ../dev -q
    fi
} 2>&1 | tee "$f"

# if there's an issue in base_include 'go' won't be defined
# if there's an issue in include_printers it will be an undefined printer
if ! grep -q -F 'val go : unit -> unit = <fun>' "$f" ||
        grep -q -E "Error|Unbound" "$f";
then exit 1; fi
