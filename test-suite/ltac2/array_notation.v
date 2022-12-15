Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].

Ltac2 check_eq_int_array(a1: int array)(a2: int array) :=
  if Array.equal Int.equal a1 a2 then () else Control.throw Regression_Test_Failure.

Goal True.
  check_eq_int_array [| 1; 22; 333 |] (Array.of_list [1; 22; 333]).
  check_eq_int_array [| 22 |] (Array.of_list [22]).
  check_eq_int_array [| |] (Array.of_list []). (* space between [| and |] is mandatory *)
  constructor.
Qed.

(* Test that tactic dispatch where "[|" is two tokens still works: *)

Goal True /\ True.
Proof.
  split > [|constructor]. constructor.
Qed.

Goal forall a b: nat, a = b -> True /\ a = b /\ True.
Proof.
  intros.
  (split > [|split]) > [|exact H|].
  all: constructor.
Qed.

Set Default Proof Mode "Classic".

Goal True /\ True.
Proof.
  split; [|constructor]. constructor.
Qed.

Goal forall a b: nat, a = b -> True /\ a = b /\ True.
Proof.
  intros.
  (split; [|split]); [|exact H|].
  all: constructor.
Qed.
