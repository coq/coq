(* Check exportation of Argument Scopes even without import of modules *)

Require Import ZArith.

Module A.
Definition opp := Z.opp.
End A.
Check (A.opp 3).

(* Test extra scopes to be used in the presence of coercions *)

Record B := { f :> Z -> Z }.
Variable a:B.
Arguments a _%_Z_scope : extra scopes.
Check a 0.

(* Check that casts activate scopes if ever possible *)

Inductive U := A.
Bind Scope u with U.
Notation "'ε'" := A : u.
Definition c := ε : U.

(* Check activation of type scope for tactics such as assert *)

Goal True.
assert (nat * nat).
Abort.

(* Check propagation of scopes in indirect applications to references *)

Module PropagateIndirect.
Notation "0" := true : bool_scope.

Axiom f : bool -> bool -> nat.
Check (@f 0) 0.

Record R := { p : bool -> nat }.
Check fun r => r.(@p) 0.
End PropagateIndirect.

Module ScopeProjNotation.

Declare Scope foo_scope.
Delimit Scope foo_scope with foo.
Record prod A B := pair { fst : A ; snd : B }.
Notation "[[ t , u ]]" := (pair _ _ t u) : foo_scope.
Arguments fst {A B} p%_foo.
Check [[2,3]].(fst).

End ScopeProjNotation.
