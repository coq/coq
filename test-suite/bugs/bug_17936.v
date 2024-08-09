From Stdlib Require Import Lia ZArith Zify PreOmega.
Open Scope Z_scope.

Goal forall m n, n * m = 1 -> n = 1 \/ n = -1.
  pose proof Z.mul_eq_1; intros.
  Z.to_euclidean_division_equations.
  Fail assumption. (* was previously succeeding *)
  let T := type of Z.mul_eq_1 in
  lazymatch goal with
  | [ H : T |- _ ] => idtac
  | _ => fail 0 "Z.to_euclidean_division_equations should not mangle dependent quantifiers"
  end.
Abort.
(* swapped n m order *)
Goal forall n m, n * m = 1 -> n = 1 \/ n = -1.
  pose proof Z.mul_eq_1; intros.
  Z.to_euclidean_division_equations.
  Fail assumption. (* correctly does not succeed *)
  let T := type of Z.mul_eq_1 in
  lazymatch goal with
  | [ H : T |- _ ] => idtac
  | _ => fail 0 "Z.to_euclidean_division_equations should not mangle dependent quantifiers"
  end.
Abort.

(* Test that the commit message suggestion in fact works to restore behavior *)
Ltac saturate :=
  let unique_pose_proof lem :=
    let ty := type of lem in
    lazymatch goal with
    | [ H : ty |- _ ] => fail
    | _ => pose proof lem
    end in
  repeat match goal with
    | [ H : forall x : ?T, _, H' : ?T |- _ ] => unique_pose_proof (H H')
    | [ H : forall a (x : ?T), _, H' : ?T |- _ ] => unique_pose_proof (fun a => H a H')
    end.
Ltac Zify.zify_internal_to_euclidean_division_equations ::= Z.to_euclidean_division_equations; saturate.
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations; saturate.
Goal forall m n, n * m = 1 -> n = 1 \/ n = -1.
  pose proof Z.mul_eq_1; intros.
  zify.
  assumption.
Qed.

(* swapped n m order *)
Goal forall n m, n * m = 1 -> n = 1 \/ n = -1.
  pose proof Z.mul_eq_1; intros.
  zify.
  assumption.
Qed.
