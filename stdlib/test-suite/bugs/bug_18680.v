Set Universe Polymorphism.

From Stdlib Require Import PeanoNat.
From Stdlib Require Import JMeq.

Inductive narray {X : Type} : nat -> Type :=
    | Elt : X -> narray 0
    | Cons {c : nat} (x : X) (n : narray c) : narray (c + 1).

Lemma eqb_eq : forall x, Nat.eqb x x = true.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. apply IHx.
Qed.

Lemma sub_still_le : forall x y,
  Nat.eqb x y = false -> x <= y -> x + 1 <= y.
Proof.
  intros x y NatEq xLey.
  induction xLey.
  - rewrite eqb_eq in NatEq. discriminate NatEq.
  - replace (x + 1) with (S x).
    * apply le_n_S. apply xLey.
    * rewrite Nat.add_comm. simpl. reflexivity.
Qed.

(* Returns the nth element of the array; this version works. *)
Program Fixpoint get
   {X : Type} {sz : nat}
   (get_n : nat) (cpt : nat) (l : narray sz) : X :=
    match l with
    | Elt x => x
    | Cons x tl =>
      match Nat.eqb get_n cpt with
      | true => x
      | false =>
        get get_n (cpt + 1) tl
    end
  end.

(* Same than get, but carries additional proofs. *)
Succeed Program Fixpoint get'
   {X : Type} {sz : nat}
   (get_n : nat)
   (Inv : get_n < sz)
   (cpt : nat)
   (P : cpt <= get_n)
   (l : narray sz) : X :=
    match l with
    | Elt x => x
    | Cons x tl =>
      match Nat.eqb get_n cpt with
      | true => x
      | false =>
        let CondFalse: Nat.eqb get_n cpt = false := _ in
        let P' : cpt + 1 <= get_n :=
          sub_still_le cpt get_n CondFalse P
        in
        get' get_n Inv (cpt + 1) P' tl
    end
  end.
