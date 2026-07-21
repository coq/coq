Declare ML Module "coq-test-suite.elim_flag".

(* With elimination checking on, the large elimination below is squashed. *)
Inductive checked_or (A B : Prop) : Prop :=
| checked_l : A -> checked_or A B
| checked_r : B -> checked_or A B.

Fail Definition checked_large (A B : Prop) (H : checked_or A B) : Type :=
  match H with
  | checked_l _ _ _ => nat
  | checked_r _ _ _ => bool
  end.

Print Assumptions checked_or.

(* The plugin disables check_eliminations directly, the way rocq-lean-import
   does; there is intentionally no vernacular setter for this flag. *)
Unset Test Elimination Checking.

Inductive unchecked_or (A B : Prop) : Prop :=
| unchecked_l : A -> unchecked_or A B
| unchecked_r : B -> unchecked_or A B.

Definition unchecked_large (A B : Prop) (H : unchecked_or A B) : Type :=
  match H with
  | unchecked_l _ _ _ => nat
  | unchecked_r _ _ _ => bool
  end.

Set Test Elimination Checking.

Print Assumptions unchecked_large.

Set Printing All Assumptions.
Print Assumptions unchecked_large.
Unset Printing All Assumptions.

Print Typing Flags.
