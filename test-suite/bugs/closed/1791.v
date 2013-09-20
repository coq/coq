(* simpl performs eta expansion *)

Set Implicit Arguments.
Require Import List.

Definition k0 := Set.
Definition k1 := k0 -> k0.

(** iterating X n times *)
Fixpoint Pow (X:k1)(k:nat){struct k}:k1:=
  match k with 0 => fun X => X
             |  S k' => fun A => X (Pow X k' A)
  end.

Parameter Bush: k1.
Parameter BushToList: forall (A:k0), Bush A ->  list A.

Definition BushnToList (n:nat)(A:k0)(t:Pow Bush n A): list A.
Proof.
  intros.
  induction n.
  exact (t::nil).
  simpl in t.
  exact (flat_map IHn (BushToList t)).
Defined.

Parameter bnil : forall (A:k0), Bush A.
Axiom BushToList_bnil: forall (A:k0), BushToList (bnil A) = nil(A:=A).

Lemma BushnToList_bnil (n:nat)(A:k0):
  BushnToList (S n) A (bnil (Pow Bush n A)) = nil.
Proof.
  intros.
  simpl.
  rewrite BushToList_bnil.
  simpl.
  reflexivity.
Qed.
