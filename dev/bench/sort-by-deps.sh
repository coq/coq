#!/usr/bin/env bash

program_name="$0"
program_path=$(readlink -f "${program_name%/*}")

# We add || true (which may not be needed without set -e) to be
# explicit about the fact that this script does not fail even if `opam
# install --show-actions` does, e.g., because of a non-existent
# package
#
# TODO: Figure out how to use the OPAM API
# (https://opam.ocaml.org/doc/api/) to call this from OCaml.
for i in "$@"; do
    echo -n "$i:"; ((echo -n "$(opam install --show-actions "$i" | grep -o '∗\s*install\s*[^ ]*' | sed 's/∗\s*install\s*//g')" | tr '\n' ',') || true); echo
done | xargs ocaml "${program_path}/sort-by-deps"
