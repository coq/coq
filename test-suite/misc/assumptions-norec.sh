#!/usr/bin/env bash

# Admitting a dependency must preserve its actual axioms without treating
# implemented fields of sealed modules as axioms. See #22569.
set -eu

D=misc/assumptions-norec
d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
cp "$D"/*.v "$d/"

$coqc -noinit -Q "$d" AssumptionsNorec "$d/Defs.v"
$coqc -noinit -Q "$d" AssumptionsNorec "$d/Use.v"

cat > "$d/expected" <<'EOF'
AssumptionsNorec.Defs.Abstract.value
AssumptionsNorec.Defs.WithAxiom.hidden
AssumptionsNorec.Defs.declared
EOF

check_axioms () {
  "$BIN"rocqchk -silent -o -Q "$d" AssumptionsNorec "$@" > "$d/out.log" 2>&1
  sed -n '/^\* Axioms:/,/^\* Constants/ s/^    //p' "$d/out.log" |
    LC_ALL=C sort > "$d/axioms"
  diff -u "$d/expected" "$d/axioms"
}

check_axioms AssumptionsNorec.Use
check_axioms -norec AssumptionsNorec.Use
check_axioms -admit AssumptionsNorec.Defs AssumptionsNorec.Use
