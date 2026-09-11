Require Import ssreflect.

Set Warnings "+remaining-shelved-goals".

Lemma foo {x : Prop} : x -> x.
Proof. eauto. Qed.

(* Sanity check: direct [apply: foo] does not leave a shelved goal. *)
Goal True -> True.
Proof.
  apply: foo.
  Unshelve.
Qed.

Tactic Notation "use" open_constr(H) := apply: H.
Tactic Notation "use_apply" open_constr(H) := apply H.
Tactic Notation "use_eapply" open_constr(H) := eapply H.
Tactic Notation "use_pose_ann" open_constr(H) :=
  pose H; apply: H (_ : list _).

Lemma const2 {A : Type} (x : A) : True.
Proof. exact I. Qed.

(* Going through [Tactic Notation] with [open_constr] should behave like the
   direct ssreflect tactic: the implicit argument evar created while reading
   [H] must be consumed when [apply: H] instantiates it. *)
Goal True -> True.
Proof.
  use foo.
Qed.

(* Ordinary Ltac apply/eapply are controls documenting the expected behavior. *)
Goal True -> True.
Proof.
  use_apply foo.
Qed.

Goal True -> True.
Proof.
  use_eapply foo.
Qed.

Section OldAliasOrientation.
Variable P : nat -> nat -> Prop.

Goal (forall a b, P a b -> True) ->
     (forall k, k <= 0 -> True -> P k k) -> True.
Proof.
  move=> H HP.
  eapply H.
  apply: HP.
  - exact: le_n.
  - exact I.
Qed.
End OldAliasOrientation.

(* The old implicit [A] is defined as [list ?T], where [?T] is fresh while
   reading the ssreflect term; [?T] must become a real destination goal. *)
Goal True.
Proof.
  use_pose_ann const2.
  Fail Qed.
  exact (@nil nat).
Qed.

Lemma needs {P : Prop} : P -> True.
Proof. auto. Qed.

(* Real premises should still be exposed as focused goals, not hidden as
   shelved or otherwise invisible evars. *)
Goal True.
Proof.
  apply: needs.
  exact I.
Qed.

Goal True.
Proof.
  use needs.
  exact I.
Qed.

(* Incomplete applications must still fail to close. *)
Goal True.
Proof.
  apply: needs.
  Fail Qed.
Abort.

Goal True.
Proof.
  use needs.
  Fail Qed.
Abort.
