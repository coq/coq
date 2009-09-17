(* Calls to external decision procedures *)

Require Export ZArith.
Require Export Classical.

(* Zenon *)

(*  Copyright 2004 INRIA  *)
(*  $Id$  *)

Lemma zenon_nottrue :
  (~True -> False).
Proof. tauto. Qed.

Lemma zenon_noteq : forall (T : Type) (t : T),
  ((t <> t) -> False).
Proof. tauto. Qed.

Lemma zenon_and : forall P Q : Prop,
  (P -> Q -> False) -> (P /\ Q -> False).
Proof. tauto. Qed.

Lemma zenon_or : forall P Q : Prop,
  (P -> False) -> (Q -> False) -> (P \/ Q -> False).
Proof. tauto. Qed.

Lemma zenon_imply : forall P Q : Prop,
  (~P -> False) -> (Q -> False) -> ((P -> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_equiv : forall P Q : Prop,
  (~P -> ~Q -> False) -> (P -> Q -> False) -> ((P <-> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notand : forall P Q : Prop,
  (~P -> False) -> (~Q -> False) -> (~(P /\ Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notor : forall P Q : Prop,
  (~P -> ~Q -> False) -> (~(P \/ Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notimply : forall P Q : Prop,
  (P -> ~Q -> False) -> (~(P -> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_notequiv : forall P Q : Prop,
  (~P -> Q -> False) -> (P -> ~Q -> False) -> (~(P <-> Q) -> False).
Proof. tauto. Qed.

Lemma zenon_ex : forall (T : Type) (P : T -> Prop),
  (forall z : T, ((P z) -> False)) -> ((exists x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_all : forall (T : Type) (P : T -> Prop) (t : T),
  ((P t) -> False) -> ((forall x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_notex : forall (T : Type) (P : T -> Prop) (t : T),
  (~(P t) -> False) -> (~(exists x : T, (P x)) -> False).
Proof. firstorder. Qed.

Lemma zenon_notall : forall (T : Type) (P : T -> Prop),
  (forall z : T, (~(P z) -> False)) -> (~(forall x : T, (P x)) -> False).
Proof. intros T P Ha Hb. apply Hb. intro. apply NNPP. exact (Ha x). Qed.

Lemma zenon_equal_base : forall (T : Type) (f : T), f = f.
Proof. auto. Qed.

Lemma zenon_equal_step :
  forall (S T : Type) (fa fb : S -> T) (a b : S),
  (fa = fb) -> (a <> b -> False) -> ((fa a) = (fb b)).
Proof. intros. rewrite (NNPP (a = b)). congruence. auto. Qed.

Lemma zenon_pnotp : forall P Q : Prop,
  (P = Q) -> (P -> ~Q -> False).
Proof. intros P Q Ha. rewrite Ha. auto. Qed.

Lemma zenon_notequal : forall (T : Type) (a b : T),
  (a = b) -> (a <> b -> False).
Proof. auto. Qed.

Ltac zenon_intro id :=
  intro id || let nid := fresh in (intro nid; clear nid)
.

Definition zenon_and_s := fun P Q a b => zenon_and P Q b a.
Definition zenon_or_s := fun P Q a b c => zenon_or P Q b c a.
Definition zenon_imply_s := fun P Q a b c => zenon_imply P Q b c a.
Definition zenon_equiv_s := fun P Q a b c => zenon_equiv P Q b c a.
Definition zenon_notand_s := fun P Q a b c => zenon_notand P Q b c a.
Definition zenon_notor_s := fun P Q a b => zenon_notor P Q b a.
Definition zenon_notimply_s := fun P Q a b => zenon_notimply P Q b a.
Definition zenon_notequiv_s := fun P Q a b c => zenon_notequiv P Q b c a.
Definition zenon_ex_s := fun T P a b => zenon_ex T P b a.
Definition zenon_notall_s := fun T P a b => zenon_notall T P b a.

Definition zenon_pnotp_s := fun P Q a b c => zenon_pnotp P Q c a b.
Definition zenon_notequal_s := fun T a b x y => zenon_notequal T a b y x.

(* Ergo *)

Set Implicit Arguments.
Section congr.
  Variable t:Type.
Lemma ergo_eq_concat_1 :
  forall (P:t -> Prop) (x y:t),
    P x -> x = y -> P y.
Proof.
  intros; subst; auto.
Qed.

Lemma ergo_eq_concat_2 :
  forall (P:t -> t -> Prop) (x1 x2 y1 y2:t),
    P x1 x2 -> x1 = y1 -> x2 = y2 -> P y1 y2.
Proof.
  intros; subst; auto.
Qed.

End congr.
