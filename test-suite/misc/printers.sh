#!/bin/sh

command -v "coqtop.byte" || { echo "Missing coqtop.byte"; exit 1; }

f=$(mktemp)
{
    printf 'Drop.\n#directory "../../dev";;\n#use "include";;\n#quit;;\n' | "coqtop.byte" -q
} 2>&1 | tee "$f"

echo $CAML_LD_LIBRARY_PATH

# if there's an issue in base_include 'go' won't be defined
# if there's an issue in include_printers it will be an undefined printer
if ! grep -q -F 'val go : unit -> unit = <fun>' "$f" ||
        grep -q -E "Error|Unbound" "$f";
then exit 1; fi
