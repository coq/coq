(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Mult.
Require Import Ring_base.
Set Implicit Arguments.
Require Import InitialRing.
Export Ring_tac.

Ltac isnatcst t :=
  let t := eval hnf in t in
  match t with
    O => true
  | S ?p => isnatcst p
  | _ => false
  end.
Ltac natcst t :=
  match isnatcst t with
    true => t
  | _ => NotConstant
  end.

Ltac Ss_to_add f acc :=
  match f with
  | S ?f1 => Ss_to_add f1 (S acc)
  | _ => constr:(acc + f)%nat
  end.

Ltac natprering :=
  match goal with
    |- context C [S ?p] =>
    match p with
      O => fail 1 (* avoid replacing 1 with 1+0 ! *)
    | p => match isnatcst p with 
           | true => fail 1
           | false => let v := Ss_to_add p (S 0) in
                         fold v; natprering
           end
    end
  | _ => idtac
  end.

 Lemma natSRth : semi_ring_theory O (S O) plus mult (@eq nat).
 Proof.
  constructor. exact plus_0_l. exact plus_comm. exact plus_assoc.
  exact mult_1_l. exact mult_0_l. exact mult_comm. exact mult_assoc.
  exact mult_plus_distr_r. 
 Qed.


Unboxed Fixpoint nateq (n m:nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => nateq n' m'
  | _, _ => false
  end.

Lemma nateq_ok : forall n m:nat, nateq n m = true -> n = m.
Proof.
  simple induction n; simple induction m; simpl; intros; try discriminate.
  trivial.
  rewrite (H n1 H1).
  trivial.
Qed.

Add Ring natr : natSRth
  (decidable nateq_ok, constants [natcst], preprocess [natprering]).
