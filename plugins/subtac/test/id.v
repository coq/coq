Require Coq.Arith.Arith.

Require Import Coq.subtac.Utils.
Program Fixpoint id (n : nat) : { x : nat | x = n } :=
  match n with
  | O => O
  | S p => S (id p)
  end.
intros ; auto.

pose (subset_simpl (id p)).
simpl in e.
unfold p0.
rewrite e.
auto.
Defined.

Check id.
Print id.
Extraction id.

Axiom le_gt_dec : forall n m, { n <= m } + { n > m }.
Require Import Omega.

Program Fixpoint id_if (n : nat) { wf n lt }: { x : nat | x = n } :=
  if le_gt_dec n 0 then 0
  else S (id_if (pred n)).
intros.
auto with arith.
intros.
pose (subset_simpl (id_if (pred n))).
simpl in e.
rewrite e.
induction n ; auto with arith.
Defined.

Print id_if_instance.
Extraction id_if_instance.

Notation "( x & y )" := (@existS _ _ x y) : core_scope.

Program Definition testsig ( a : nat ) : { x : nat & { y : nat | x = y }} :=
  (a & a).
intros.
auto.
Qed.
