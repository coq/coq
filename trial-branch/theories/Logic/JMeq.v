(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** John Major's Equality as proposed by Conor McBride

  Reference:

  [McBride] Elimination with a Motive, Proceedings of TYPES 2000,
  LNCS 2277, pp 197-216, 2002.

*)

Set Implicit Arguments.

Unset Elimination Schemes.

Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
    JMeq_refl : JMeq x x.

Set Elimination Schemes.

Hint Resolve JMeq_refl.

Lemma sym_JMeq : forall (A B:Type) (x:A) (y:B), JMeq x y -> JMeq y x.
destruct 1; trivial.
Qed.

Hint Immediate sym_JMeq.

Lemma trans_JMeq :
 forall (A B C:Type) (x:A) (y:B) (z:C), JMeq x y -> JMeq y z -> JMeq x z.
destruct 1; trivial.
Qed.

Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.

Lemma JMeq_ind : forall (A:Type) (x y:A) (P:A -> Prop), P x -> JMeq x y -> P y.
intros A x y P H H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Type) (x y:A) (P:A -> Set), P x -> JMeq x y -> P y.
intros A x y P H H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rect : forall (A:Type) (x y:A) (P:A->Type), P x -> JMeq x y -> P y.
intros A x y P H H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r :
 forall (A:Type) (x y:A) (P:A -> Prop), P y -> JMeq x y -> P x.
intros A x y P H H'; case JMeq_eq with (1 := sym_JMeq H'); trivial.
Qed.

Lemma JMeq_rec_r :
 forall (A:Type) (x y:A) (P:A -> Set), P y -> JMeq x y -> P x.
intros A x y P H H'; case JMeq_eq with (1 := sym_JMeq H'); trivial.
Qed.

Lemma JMeq_rect_r :
 forall (A:Type) (x y:A) (P:A -> Type), P y -> JMeq x y -> P x.
intros A x y P H H'; case JMeq_eq with (1 := sym_JMeq H'); trivial.
Qed.

(** [JMeq] is equivalent to [eq_dep Type (fun X => X)] *)

Require Import Eqdep.

Lemma JMeq_eq_dep_id :
 forall (A B:Type) (x:A) (y:B), JMeq x y -> eq_dep Type (fun X => X) A x B y.
Proof.
destruct 1.
apply eq_dep_intro.
Qed.

Lemma eq_dep_id_JMeq :
 forall (A B:Type) (x:A) (y:B), eq_dep Type (fun X => X) A x B y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

(** [eq_dep U P p x q y] is strictly finer than [JMeq (P p) x (P q) y] *)

Lemma eq_dep_JMeq :
 forall U P p x q y, eq_dep U P p x q y -> JMeq x y.
Proof.
destruct 1.
apply JMeq_refl.
Qed.

Lemma eq_dep_strictly_stronger_JMeq :
 exists U, exists P, exists p, exists q, exists x, exists y,
  JMeq x y /\ ~ eq_dep U P p x q y.
Proof.
exists bool. exists (fun _ => True). exists true. exists false.
exists I. exists I.
split.
trivial.
intro H.
assert (true=false) by (destruct H; reflexivity).
discriminate.
Qed.
