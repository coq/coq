(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** John Major's Equality as proposed by C. Mc Bride

  Reference:

  [McBride] Elimination with a Motive, Proceedings of TYPES 2000,
  LNCS 2277, pp 197-216, 2002.

*)

Set Implicit Arguments.

Inductive JMeq (A:Set) (x:A) : forall B:Set, B -> Prop :=
    JMeq_refl : JMeq x x.
Reset JMeq_ind.

Hint Resolve JMeq_refl.

Lemma sym_JMeq : forall (A B:Set) (x:A) (y:B), JMeq x y -> JMeq y x.
destruct 1; trivial.
Qed.

Hint Immediate sym_JMeq.

Lemma trans_JMeq :
 forall (A B C:Set) (x:A) (y:B) (z:C), JMeq x y -> JMeq y z -> JMeq x z.
destruct 1; trivial.
Qed.

Axiom JMeq_eq : forall (A:Set) (x y:A), JMeq x y -> x = y.

Lemma JMeq_ind : forall (A:Set) (x y:A) (P:A -> Prop), P x -> JMeq x y -> P y.
intros A x y P H H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Set) (x y:A) (P:A -> Set), P x -> JMeq x y -> P y.
intros A x y P H H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r :
 forall (A:Set) (x y:A) (P:A -> Prop), P y -> JMeq x y -> P x.
intros A x y P H H'; case JMeq_eq with (1 := sym_JMeq H'); trivial.
Qed.

Lemma JMeq_rec_r :
 forall (A:Set) (x y:A) (P:A -> Set), P y -> JMeq x y -> P x.
intros A x y P H H'; case JMeq_eq with (1 := sym_JMeq H'); trivial.
Qed.

(** [JMeq] is equivalent to [(eq_dep Set [X]X)] *)

Require Import Eqdep.

Lemma JMeq_eq_dep :
 forall (A B:Set) (x:A) (y:B), JMeq x y -> eq_dep Set (fun X => X) A x B y.
Proof.
destruct 1.
apply eq_dep_intro.
Qed.

Lemma eq_dep_JMeq :
 forall (A B:Set) (x:A) (y:B), eq_dep Set (fun X => X) A x B y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl. 
Qed.
