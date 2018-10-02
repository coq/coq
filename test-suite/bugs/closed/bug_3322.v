Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 11971 lines to 11753 lines, then from 7702 lines to 564 lines, then from 571 lines to 61 lines *)
Set Asymmetric Patterns.
Axiom admit : forall {T}, T.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : (projT1 u) = (projT1 v) &  transport _ p (projT2 u) = (projT2 v)})
: u = v.
Proof.
  destruct pq as [p q], u as [x y], v as [x' y']; simpl in *.
  destruct p, q; simpl; reflexivity.
Defined.
Arguments path_sigma_uncurried : simpl never.
Section opposite.
  Let opposite_functor_involutive_helper
    := @path_sigma_uncurried admit admit (existT _ admit admit) admit (existT _ admit admit).

  Goal True.
  Opaque path_sigma_uncurried.
  simpl in *.
  Transparent path_sigma_uncurried.
  (* This command should fail with "Error: Failed to progress.", as it does in 8.4; the simpl never directive should prevent simpl from progressing *)
  Fail progress simpl in *.
