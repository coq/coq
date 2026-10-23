#!/usr/bin/env bash

# rocqchk must not trust a serialized module's delta resolver to establish that
# incompatible declarations have the same canonical name.

set -e

D=misc/rocqchk-delta-alias

rm -f "$D"/good/*.vo "$D"/good/*.vok "$D"/good/*.vos "$D"/good/*.glob \
      "$D"/bad/*.vo "$D"/bad/*.vok "$D"/bad/*.vos "$D"/bad/*.glob \
      "$D"/out.log

for kind in constant inductive; do
  $coqc -noinit -R "$D/good" DeltaAlias "$D/good/Attack.v"
  $coqc -noinit -R "$D/bad" DeltaAlias "$D/bad/Attack.v"
  ocaml "$D/forge.ml" "$D/good/Attack.vo" "$D/bad/Attack.vo" "$kind"

  if "$BIN"rocqchk -R "$D/good" DeltaAlias DeltaAlias.Attack > "$D/out.log" 2>&1; then
    echo "rocqchk accepted a forged $kind delta alias and a closed proof of False"
    cat "$D/out.log"
    exit 1
  fi

  if ! grep -q "Module typing error" "$D/out.log"; then
    echo "unexpected rocqchk failure for a forged $kind alias"
    cat "$D/out.log"
    exit 1
  fi
done
