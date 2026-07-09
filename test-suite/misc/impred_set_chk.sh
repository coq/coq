#!/usr/bin/env bash

# Check that rocq check validates the impredicative-Set usage bits
# stored in vo files (cf Constr.const_uses_impredicative_set and the
# opaque proof term bit).

set -e

export PATH=$BIN:$PATH

cd misc/impred_set_chk
rm -f *.vo
rocq compile -impredicative-set -R . TestImpredChk impred_lib.v
rocq check -impredicative-set -R . TestImpredChk TestImpredChk.impred_lib
