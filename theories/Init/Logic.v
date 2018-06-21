(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

Require Export Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

(** [True] is the always true proposition *)

Inductive True : Prop :=
  I : True.

(** [False] is the always false proposition *)
Inductive False : Prop :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

(** Create the "core" hint database, and set its transparent state for
  variables and constants explicitely. *)

Create HintDb core.
Hint Variables Opaque : core.
Hint Constants Opaque : core.

Hint Unfold not: core.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

Section Conjunction.

  Variables A B : Prop.

  Theorem proj1 : A /\ B -> A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem proj2 : A /\ B -> B.
  Proof.
    destruct 1; trivial.
  Qed.

End Conjunction.

(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B

where "A \/ B" := (or A B) : type_scope.

Arguments or_introl [A B] _, [A] B _.
Arguments or_intror [A B] _, A [B] _.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B:Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Section Equivalence.

Theorem iff_refl : forall A:Prop, A <-> A.
  Proof.
    split; auto.
  Qed.

Theorem iff_trans : forall A B C:Prop, (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros A B C [H1 H2] [H3 H4]; split; auto.
  Qed.

Theorem iff_sym : forall A B:Prop, (A <-> B) -> (B <-> A).
  Proof.
    intros A B [H1 H2]; split; auto.
  Qed.

End Equivalence.

Hint Unfold iff: extcore.

(** Backward direction of the equivalences above does not need assumptions *)

Theorem and_iff_compat_l : forall A B C : Prop,
  (B <-> C) -> (A /\ B <-> A /\ C).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ assumption | ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem and_iff_compat_r : forall A B C : Prop,
  (B <-> C) -> (B /\ A <-> C /\ A).
Proof.
  intros ? ? ? [Hl Hr]; split; intros [? ?]; (split; [ | assumption ]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_l : forall A B C : Prop,
  (B <-> C) -> (A \/ B <-> A \/ C).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left; assumption| right]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem or_iff_compat_r : forall A B C : Prop,
  (B <-> C) -> (B \/ A <-> C \/ A).
Proof.
  intros ? ? ? [Hl Hr]; split; (intros [?|?]; [left| right; assumption]);
  [apply Hl | apply Hr]; assumption.
Qed.

Theorem imp_iff_compat_l : forall A B C : Prop,
  (B <-> C) -> ((A -> B) <-> (A -> C)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply Hl | apply Hr]; apply H; assumption.
Qed.

Theorem imp_iff_compat_r : forall A B C : Prop,
  (B <-> C) -> ((B -> A) <-> (C -> A)).
Proof.
  intros ? ? ? [Hl Hr]; split; intros H ?; [apply H, Hr | apply H, Hl]; assumption.
Qed.

Theorem not_iff_compat : forall A B : Prop,
  (A <-> B) -> (~ A <-> ~B).
Proof.
  intros; apply imp_iff_compat_r; assumption.
Qed.


(** Some equivalences *)

Theorem neg_false : forall A : Prop, ~ A <-> (A <-> False).
Proof.
  intro A; unfold not; split.
  - intro H; split; [exact H | intro H1; elim H1].
  - intros [H _]; exact H.
Qed.

Theorem and_cancel_l : forall A B C : Prop,
  (B -> A) -> (C -> A) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_l]; intros [HypL HypR]; split; intros.
  + apply HypL; split; [apply Hl | ]; assumption.
  + apply HypR; split; [apply Hr | ]; assumption.
Qed.

Theorem and_cancel_r : forall A B C : Prop,
  (B -> A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
Proof.
  intros A B C Hl Hr.
  split; [ | apply and_iff_compat_r]; intros [HypL HypR]; split; intros.
  + apply HypL; split; [ | apply Hl ]; assumption.
  + apply HypR; split; [ | apply Hr ]; assumption.
Qed.

Theorem and_comm : forall A B : Prop, A /\ B <-> B /\ A.
Proof.
  intros; split; intros [? ?]; split; assumption.
Qed.

Theorem and_assoc : forall A B C : Prop, (A /\ B) /\ C <-> A /\ B /\ C.
Proof.
  intros; split; [ intros [[? ?] ?]| intros [? [? ?]]]; repeat split; assumption.
Qed.

Theorem or_cancel_l : forall A B C : Prop,
  (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_l]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ right | destruct Fl | ]; assumption. }
  { destruct Hr; [ right | destruct Fr | ]; assumption. }
Qed.

Theorem or_cancel_r : forall A B C : Prop,
  (B -> ~ A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_r]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ left | | destruct Fl ]; assumption. }
  { destruct Hr; [ left | | destruct Fr ]; assumption. }
Qed.

Theorem or_comm : forall A B : Prop, (A \/ B) <-> (B \/ A).
Proof.
  intros; split; (intros [? | ?]; [ right | left ]; assumption).
Qed.

Theorem or_assoc : forall A B C : Prop, (A \/ B) \/ C <-> A \/ B \/ C.
Proof.
  intros; split; [ intros [[?|?]|?]| intros [?|[?|?]]].
  + left; assumption.
  + right; left; assumption.
  + right; right; assumption.
  + left; left; assumption.
  + left; right; assumption.
  + right; assumption.
Qed.
Lemma iff_and : forall A B : Prop, (A <-> B) -> (A -> B) /\ (B -> A).
Proof.
  intros A B []; split; trivial.
Qed.

Lemma iff_to_and : forall A B : Prop, (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
  intros; split; intros [Hl Hr]; (split; intros; [ apply Hl | apply Hr]); assumption.
Qed.

(** [(IF_then_else P Q R)], written [IF P then Q else R] denotes
    either [P] and [Q], or [~P] and [R] *)

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.

(** * First-order quantifiers *)

(** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].

    Universal quantification is primitively written [forall x:A, Q]. By
    symmetry with existential quantification, the construction [all P]
    is provided too.
*)

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.

Definition all (A:Type) (P:A -> Prop) := forall x:A, P x.

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

Notation "'exists2' ' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.
Notation "'exists2' ' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x strict pattern, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(** Derived rules for universal quantification *)

Section universal_quantification.

  Variable A : Type.
  Variable P : A -> Prop.

  Theorem inst : forall x:A, all (fun x => P x) -> P x.
  Proof.
    unfold all; auto.
  Qed.

  Theorem gen : forall (B:Prop) (f:forall y:A, B -> P y), B -> all P.
  Proof.
    red; auto.
  Qed.

End universal_quantification.

(** * Equality *)

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.

Hint Resolve I conj or_introl or_intror : core.
Hint Resolve eq_refl: core.
Hint Resolve ex_intro ex_intro2: core.

Section Logic_lemmas.

  Theorem absurd : forall A C:Prop, A -> ~ A -> C.
  Proof.
    unfold not; intros A C h1 h2.
    destruct (h2 h1).
  Qed.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

  End equality.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

End EqNotations.

Import EqNotations.

Lemma rew_opp_r : forall A (P:A->Type) (x y:A) (H:x=y) (a:P y), rew H in rew <- H in a = a.
Proof.
intros.
destruct H.
reflexivity.
Defined.

Lemma rew_opp_l : forall A (P:A->Type) (x y:A) (H:x=y) (a:P x), rew <- H in rew H in a = a.
Proof.
intros.
destruct H.
reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal_compose : forall A B C (a b:A) (f:A->B) (g:B->C) (e:a=b),
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

(** The groupoid structure of equality *)

Theorem eq_trans_refl_l : forall A (x y:A) (e:x=y), eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r : forall A (x y:A) (e:x=y), eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_sym_involutive : forall A (x y:A) (e:x=y), eq_sym (eq_sym e) = e.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_l : forall A (x y:A) (e:x=y), eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r : forall A (x y:A) (e:x=y), eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc : forall A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t),
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined.

(** Extra properties of equality *)

Theorem eq_id_comm_l : forall A (f:A->A) (Hf:forall a, a = f a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  intros.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Theorem eq_id_comm_r : forall A (f:A->A) (Hf:forall a, f a = a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  intros.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf (f (f a)))).
  set (Hfsymf := fun a => eq_sym (Hf a)).
  change (eq_sym (Hf (f (f a)))) with (Hfsymf (f (f a))).
  pattern (Hfsymf (f (f a))).
  destruct (eq_id_comm_l f Hfsymf (f a)).
  destruct (eq_id_comm_l f Hfsymf a).
  unfold Hfsymf.
  destruct (Hf a). simpl.
  rewrite eq_trans_refl_l.
  reflexivity.
Defined.

Lemma eq_refl_map_distr : forall A B x (f:A->B), f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr : forall A B x y z (f:A->B) (e:x=y) (e':y=z), f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
destruct e'.
reflexivity.
Defined.

Lemma eq_sym_map_distr : forall A B (x y:A) (f:A->B) (e:x=y), eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
destruct e.
reflexivity.
Defined.

Lemma eq_trans_sym_distr : forall A (x y z:A) (e:x=y) (e':y=z), eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
destruct e, e'.
reflexivity.
Defined.

Lemma eq_trans_rew_distr : forall A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x),
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const : forall A P (x y:A) (e:x=y) (k:P),
    rew [fun _ => P] e in k = k.
Proof.
  destruct e; reflexivity.
Qed.


(* Aliases *)

Notation sym_eq := eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := eq_refl (only parsing).
Notation sym_equal := eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

Hint Immediate eq_sym not_eq_sym: core.

(** Basic definitions about relations and properties *)

Definition subrelation (A B : Type) (R R' : A->B->Prop) :=
  forall x y, R x y -> R' x y.

Definition unique (A : Type) (P : A->Prop) (x:A) :=
  P x /\ forall (x':A), P x' -> x=x'.

Definition uniqueness (A:Type) (P:A->Prop) := forall x y, P x -> P y -> x = y.

(** Unique existence *)

Notation "'exists' ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  !  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Lemma unique_existence : forall (A:Type) (P:A->Prop),
  ((exists x, P x) /\ uniqueness P) <-> (exists! x, P x).
Proof.
  intros A P; split.
  - intros ((x,Hx),Huni); exists x; red; auto.
  - intros (x,(Hx,Huni)); split.
    + exists x; assumption.
    + intros x' x'' Hx' Hx''; transitivity x.
      symmetry; auto.
      auto.
Qed.

Lemma forall_exists_unique_domain_coincide :
  forall A (P:A->Prop), (exists! x, P x) ->
  forall Q:A->Prop, (forall x, P x -> Q x) <-> (exists x, P x /\ Q x).
Proof.
  intros A P (x & Hp & Huniq); split.
  - intro; exists x; auto.
  - intros (x0 & HPx0 & HQx0) x1 HPx1.
    assert (H : x0 = x1) by (transitivity x; [symmetry|]; auto).
    destruct H.
    assumption.
Qed.

Lemma forall_exists_coincide_unique_domain :
  forall A (P:A->Prop),
  (forall Q:A->Prop, (forall x, P x -> Q x) <-> (exists x, P x /\ Q x))
  -> (exists! x, P x).
Proof.
  intros A P H.
  destruct H with (Q:=P) as ((x & Hx & _),_); [trivial|].
  exists x. split; [trivial|].
  destruct H with (Q:=fun x'=>x=x') as (_,Huniq).
  apply Huniq. exists x; auto.
Qed.

(** * Being inhabited *)

(** The predicate [inhabited] can be used in different contexts. If [A] is
    thought as a type, [inhabited A] states that [A] is inhabited. If [A] is
    thought as a computationally relevant proposition, then
    [inhabited A] weakens [A] so as to hide its computational meaning.
    The so-weakened proof remains computationally relevant but only in
    a propositional context.
*)

Inductive inhabited (A:Type) : Prop := inhabits : A -> inhabited A.

Hint Resolve inhabits: core.

Lemma exists_inhabited : forall (A:Type) (P:A->Prop),
  (exists x, P x) -> inhabited A.
Proof.
  destruct 1; auto.
Qed.

Lemma inhabited_covariant (A B : Type) : (A -> B) -> inhabited A -> inhabited B.
Proof.
  intros f [x];exact (inhabits (f x)).
Qed.

(** Declaration of stepl and stepr for eq and iff *)

Lemma eq_stepl : forall (A : Type) (x y z : A), x = y -> x = z -> z = y.
Proof.
  intros A x y z H1 H2. rewrite <- H2; exact H1.
Qed.

Declare Left Step eq_stepl.
Declare Right Step eq_trans.

Lemma iff_stepl : forall A B C : Prop, (A <-> B) -> (A <-> C) -> (C <-> B).
Proof.
  intros ? ? ? [? ?] [? ?]; split; intros; auto.
Qed.

Declare Left Step iff_stepl.
Declare Right Step iff_trans.

Local Notation "'rew' 'dependent' H 'in' H'"
  := (match H with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").

(** Equality for [ex] *)
Section ex.
  Local Unset Implicit Arguments.
  Definition eq_ex_uncurried {A : Type} (P : A -> Prop) {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : exists p : u1 = v1, rew p in u2 = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2.
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Qed.

  Definition eq_ex {A : Type} {P : A -> Prop} (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1) (q : rew p in u2 = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2
    := eq_ex_uncurried P (ex_intro _ p q).

  Definition eq_ex_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1)
    : ex_intro P u1 u2 = ex_intro P v1 v2
    := eq_ex u1 v1 u2 v2 p (P_hprop _ _ _).

  Lemma rew_ex {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : exists p, Q x p) {y} (H : x = y)
  : rew [fun a => exists p, Q a p] H in u
    = match u with
        | ex_intro _ u1 u2
          => ex_intro
               (Q y)
               (rew H in u1)
               (rew dependent H in u2)
      end.
  Proof.
    destruct H, u; reflexivity.
  Qed.
End ex.

(** Equality for [ex2] *)
Section ex2.
  Local Unset Implicit Arguments.

  Definition eq_ex2_uncurried {A : Type} (P Q : A -> Prop) {u1 v1 : A}
             {u2 : P u1} {v2 : P v1}
             {u3 : Q u1} {v3 : Q v1}
             (pq : exists2 p : u1 = v1, rew p in u2 = v2 & rew p in u3 = v3)
  : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3.
  Proof.
    destruct pq as [p q r].
    destruct r, q, p; simpl in *.
    reflexivity.
  Qed.

  Definition eq_ex2 {A : Type} {P Q : A -> Prop}
             (u1 v1 : A)
             (u2 : P u1) (v2 : P v1)
             (u3 : Q u1) (v3 : Q v1)
             (p : u1 = v1) (q : rew p in u2 = v2) (r : rew p in u3 = v3)
  : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3
    := eq_ex2_uncurried P Q (ex_intro2 _ _ p q r).

  Definition eq_ex2_hprop {A} {P Q : A -> Prop}
             (P_hprop : forall (x : A) (p q : P x), p = q)
             (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u1 v1 : A) (u2 : P u1) (v2 : P v1) (u3 : Q u1) (v3 : Q v1)
             (p : u1 = v1)
    : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3
    := eq_ex2 u1 v1 u2 v2 u3 v3 p (P_hprop _ _ _) (Q_hprop _ _ _).

  Lemma rew_ex2 {A x} {P : A -> Type}
        (Q : forall a, P a -> Prop)
        (R : forall a, P a -> Prop)
        (u : exists2 p, Q x p & R x p) {y} (H : x = y)
  : rew [fun a => exists2 p, Q a p & R a p] H in u
    = match u with
        | ex_intro2 _ _ u1 u2 u3
          => ex_intro2
               (Q y)
               (R y)
               (rew H in u1)
               (rew dependent H in u2)
               (rew dependent H in u3)
      end.
  Proof.
    destruct H, u; reflexivity.
  Qed.
End ex2.
