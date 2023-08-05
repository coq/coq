(* Argument names don't get mangled *)
Set Mangle Names.
Lemma leibniz_equiv_iff {A : Type} (x y : A) : True.
Proof. tauto. Qed.
Check leibniz_equiv_iff (A := nat) 2 3 : True.
Unset Mangle Names.

(* Coq doesn't make up names for arguments *)
Fail Definition bar (a a : nat) : nat := 3.
Definition bar (a a0 : nat) : nat := 3.
Arguments bar _ _ : assert.
Fail Arguments bar a a1 : assert.

(* This definition caused an anomaly in a version of this PR
without the change to prepare_implicits *)
Set Implicit Arguments.
Definition foo (_ : nat) (_ : @eq nat ltac:(assumption) 2) : True := I.
Fail Check foo (H := 2).

Definition baz (a b : nat) := b.
Arguments baz a {b}.
Set Mangle Names.
Definition baz2 (a b : nat) := b.
Arguments baz2 a {b}.
Unset Mangle Names.
