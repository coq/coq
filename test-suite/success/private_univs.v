Set Universe Polymorphism. Set Printing Universes.

Definition internal_defined@{i j | i < j +} (A : Type@{i}) : Type@{j}.
  pose(foo:=Type). (* 1 universe for the let body + 1 for the type *)
  exact A.
  Fail Defined.
Abort.

Definition internal_defined@{i j +} (A : Type@{i}) : Type@{j}.
pose(foo:=Type).
exact A.
Defined.
Check internal_defined@{_ _ _ _}.

Module M.
Lemma internal_qed@{i j|i<=j} (A:Type@{i}) : Type@{j}.
Proof.
  pose (foo := Type).
  exact A.
Qed.
Check internal_qed@{_ _}.
End M.
Include M.
(* be careful to remove const_private_univs in Include! will be coqchk'd *)

Unset Strict Universe Declaration.
Lemma private_transitivity@{i j} (A:Type@{i}) : Type@{j}.
Proof.
  pose (bar := Type : Type@{j}).
  pose (foo := Type@{i} : bar).
  exact bar.
Qed.

Definition private_transitivity'@{i j|i < j, Set < j} := private_transitivity@{i j}.
Fail Definition dummy@{i j|j <= i +} := private_transitivity@{i j}.

Unset Private Polymorphic Universes.
Lemma internal_noprivate_qed@{i j|i<=j} (A:Type@{i}) : Type@{j}.
Proof.
  pose (foo := Type).
  exact A.
  Fail Qed.
Abort.

Lemma internal_noprivate_qed@{i j +} (A:Type@{i}) : Type@{j}.
Proof.
  pose (foo := Type).
  exact A.
Qed.
Check internal_noprivate_qed@{_ _ _ _}.
