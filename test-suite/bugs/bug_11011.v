Require Import Setoid.
Require Import Corelib.Classes.CRelationClasses.
Require Import Corelib.Classes.CMorphisms.

Parameter B C : Type.
Parameter P : Type -> Type -> Type.

(* This is used for rewrites for lem_P and lem_P_iffT. *)
#[export] Instance P_Proper : Proper (iffT ==> iffT ==> iffT) (P).
Admitted.

Lemma lem_P : forall A, iffT A B -> P A C -> P B C.
Proof.
  intros A H1 H2.
  rewrite H1 in H2. (* Comment out iffT_P_Proper to see this fail. *)
Abort.

Lemma lem_P_iffT : forall A, iffT A B -> P A C -> iffT B C.
Proof.
  intros A H1 H2.
  setoid_rewrite H1 in H2.  (* Comment out iffT_P_Proper to see this fail. *)
Abort.

(* Trying to do the same with iffT instead of P. *)
#[export] Instance iffT_Proper : Proper (iffT ==> iffT ==> iffT) iffT.
Admitted.

(* Just in case? *)
#[export] Instance arrow_Proper  : Proper (iffT ==> iffT ==> iffT ) (arrow).
Admitted.

Lemma lem_iffT_P : forall A, iffT A B -> iffT A C -> P B C.
Proof.
  intros A H1 H2.
  rewrite H1 in H2.
Abort.

Lemma lem_iffT : forall A, iffT A B -> iffT A C -> iffT B C.
Proof.
  intros A H1 H2.
  setoid_rewrite H1 in H2.
Abort.
