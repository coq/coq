(* Was raising stack overflow in 8.4 and assertion failed in future 8.5 *)
Set Implicit Arguments.

Require Import List.
Require Import Coq.Program.Equality.

(** Reflexive-transitive closure ( R* ) *)

Inductive rtclosure (A : Type) (R : A-> A->Prop) : A->A->Prop :=
  | rtclosure_refl : forall x,
      rtclosure R x x
  | rtclosure_step : forall y x z,
      R x y -> rtclosure R y z -> rtclosure R x z.
  (* bug goes away if rtclosure_step is commented out *)

(** The closure of the trivial binary relation [eq] *)

Definition tr (A:Type) := rtclosure (@eq A).

(** The bug *)

Lemma bug : forall A B (l t:list A) (r s:list B),
    length l = length r ->
    tr (combine l r) (combine t s) -> tr l t.
Proof.
  intros * E Hp.
  (* bug goes away if [revert E] is called explicitly *)
  dependent induction Hp.
