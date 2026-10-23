#!/usr/bin/env bash

# -axiom-free makes the context summary actionable without changing the
# default checker policy. Regression test for #10372.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

compile() {
  local file="$d/$1.v"
  shift
  cat > "$file"
  $coqc -noinit -R "$d" AxiomFree "$@" "$file"
}

compile Safe <<'EOF'
Theorem identity : forall A : Type, forall _ : A, A.
Proof (fun A x => x).

Section Parameters.
  Variable A : Type.
  Variable x : A.
  Definition section_parameter : A := x.
End Parameters.

Module Type Signature.
  Parameter id : forall A : Type, forall _ : A, A.
End Signature.
Module Checked : Signature.
  Definition id (A : Type) (x : A) : A := x.
End Checked.
Module Parameterized (X : Signature).
  Definition id := X.id.
End Parameterized.
EOF

compile ExplicitAxiom <<'EOF'
Axiom assumed : forall A : Type, forall _ : A, A.
EOF
compile AdmittedProof <<'EOF'
Theorem unfinished : forall A : Type, forall _ : A, A.
Proof. Admitted.
EOF
compile UnsafeGuard <<'EOF'
Unset Elimination Schemes.
Inductive nat : Set := O | S (n : nat).
#[bypass_check(guard)] Fixpoint loop (n : nat) : nat := loop n.
EOF
compile UnsafeUniverses <<'EOF'
#[bypass_check(universes)] Definition bad := let t := Type in (t : t).
EOF
compile UnsafePositivity <<'EOF'
Unset Elimination Schemes.
#[bypass_check(positivity)]
Inductive bad : Type := roll : forall _ : (forall _ : bad, bad), bad.
EOF
compile Primitives <<'EOF'
Primitive int := #int63_type.
Primitive add := #int63_add.
EOF
compile UnsafeUIP <<'EOF'
Set Definitional UIP.
Definition id (A : Type) (x : A) := x.
EOF
compile SealedUnsafe <<'EOF'
Module Type Signature.
  Parameter value : Type.
End Signature.
Module Sealed : Signature.
  #[bypass_check(universes)] Definition value : Type := Type.
End Sealed.
EOF
compile SealedAxiom <<'EOF'
Module Type Signature.
  Parameter value : forall A : Type, forall _ : A, A.
End Signature.
Module Sealed : Signature.
  Axiom hidden : forall A : Type, forall _ : A, A.
  Definition value := hidden.
End Sealed.
EOF
compile Rewrite -allow-rewrite-rules <<'EOF'
Definition id (A : Type) (x : A) := x.
EOF
compile Dependency <<'EOF'
From AxiomFree Require Import ExplicitAxiom.
Definition imported := assumed.
EOF

check() {
  "$BIN"rocqchk -boot -silent -R "$d" AxiomFree "$@"
}

expect_rejection() {
  check "$@"
  if check -axiom-free "$@" > "$d/out.log" 2>&1 ||
     ! grep -q 'Axioms or unsafe features found' "$d/out.log"; then
    echo "expected axiom-free rejection: $*"
    cat "$d/out.log"
    exit 1
  fi
}

# Opaque proofs, section/functor parameters and primitives are safe.
check -axiom-free AxiomFree.Primitives
check -axiom-free -o AxiomFree.Safe > "$d/out.log" 2>&1
grep -q 'Axioms: <none>' "$d/out.log"

# Reject unused/imported axioms, admitted proofs and unsafe flags.
for lib in ExplicitAxiom AdmittedProof UnsafeGuard UnsafeUniverses \
           UnsafePositivity UnsafeUIP SealedUnsafe SealedAxiom Dependency; do
  expect_rejection "AxiomFree.$lib"
done
expect_rejection -o AxiomFree.ExplicitAxiom

# Dependencies loaded without rechecking still contribute their assumptions.
expect_rejection -norec AxiomFree.Dependency
expect_rejection -admit AxiomFree.ExplicitAxiom AxiomFree.Dependency

# Rewrite permission is unsafe even without symbols or axioms.
expect_rejection AxiomFree.Rewrite

# Impredicative Set is a supported theory, not an unsafe bypass.
check -axiom-free -impredicative-set AxiomFree.Safe
