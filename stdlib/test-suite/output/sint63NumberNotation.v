From Stdlib Require Import Uint63.
Import ZArith.

Declare Scope uint_scope.
Declare Scope sint_scope.
Delimit Scope uint_scope with uint.
Delimit Scope sint_scope with sint.

Record uint := wrapu { unwrapu : int }.
Record sint := wraps { unwraps : int }.

Definition uof_Z (v : Z) := wrapu (of_Z v).
Definition uto_Z (v : uint) := to_Z (unwrapu v).

Definition sof_Z (v : Z) := wraps (of_Z (v mod (2 ^ 31))).
Definition as_signed (bw : Z) (v : Z) :=
  (((2 ^ (bw - 1) + v) mod (2 ^ bw)) - 2 ^ (bw - 1))%Z.

Definition sto_Z (v : sint) := as_signed 31 (to_Z (unwraps v)).
Number Notation uint uof_Z uto_Z : uint_scope.
Number Notation sint sof_Z sto_Z : sint_scope.
Open Scope uint_scope.
Compute uof_Z 0.
Compute uof_Z 1.
Compute uof_Z (-1).
Check let v := 0 in v : uint.
Check let v := 1 in v : uint.
Check let v := -1 in v : uint.
Close Scope uint_scope.
Open Scope sint_scope.
Compute sof_Z 0.
Compute sof_Z 1.
Compute sof_Z (-1).
Check let v := 0 in v : sint.
Check let v := 1 in v : sint.
Check let v := -1 in v : sint.
