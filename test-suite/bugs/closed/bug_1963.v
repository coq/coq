(* Check that "dependent inversion" behaves correctly w.r.t to universes *)

Require Import Eqdep.

Set Implicit Arguments.

Inductive illist(A:Type) : nat -> Type :=
  illistn : illist A 0
| illistc : forall n:nat, A -> illist A n -> illist A (S n).

Inductive isig (A:Type)(P:A -> Type) : Type :=
  iexists : forall x : A, P x -> isig P.

Lemma inv : forall (A:Type)(n n':nat)(ts':illist A n'), n' = S n ->
  isig (fun t => isig (fun ts =>
    eq_dep nat (fun n => illist A n) n' ts' (S n) (illistc t ts))).
Proof.
intros.
dependent inversion ts'.
