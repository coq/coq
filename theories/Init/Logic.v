(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

Require Export Notations.
Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

(** [True] is the always true proposition *)

Inductive True : Prop :=
  I : True.

Register True as core.True.type.
Register I as core.True.I.

(** [False] is the always false proposition *)
Inductive False : Prop :=.

Register False as core.False.type.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Register not as core.not.type.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.

(** Create the "core" hint database, and set its transparent state for
  variables and constants explicitly. *)

Create HintDb core.
#[global]
Hint Variables Opaque : core.
#[global]
Hint Constants Opaque : core.

#[global]
Hint Unfold not: core.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

Register and as core.and.type.
Register conj as core.and.conj.

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

Register or as core.or.type.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B:Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Register iff as core.iff.type.
Register proj1 as core.iff.proj1.
Register proj2 as core.iff.proj2.

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

#[global]
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

Register ex as core.ex.type.
Register ex_intro as core.ex.intro.

Section Projections.

  Variables (A:Prop) (P:A->Prop).

  Definition ex_proj1 (x:ex P) : A :=
    match x with ex_intro _ a _ => a end.

  Definition ex_proj2 (x:ex P) : P (ex_proj1 x) :=
    match x with ex_intro _ _ b => b end.

  Register ex_proj1 as core.ex.proj1.
  Register ex_proj2 as core.ex.proj2.

End Projections.

Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.

(** [ex2] of a predicate can be projected to an [ex].

    This allows [ex_proj1] and [ex_proj2] to be usable with [ex2].

    We have two choices here: either we can set up the definition so
    that [ex_proj1] of a coerced [X : ex2 P Q] will unify with [let
    (a, _, _) := X in a] by restricting the first argument of [ex2] to
    be a [Prop], or we can define a more general [ex_of_ex2] which
    does not satisfy this conversion rule.  We choose the former,
    under the assumption that there is no reason to turn an [ex2] into
    an [ex] unless it is to project out the components. *)

Definition ex_of_ex2 (A : Prop) (P Q : A -> Prop) (X : ex2 P Q) : ex P
  := ex_intro P
              (let (a, _, _) := X in a)
              (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

Section ex2_Projections.

  Variables (A:Prop) (P Q:A->Prop).

  Definition ex_proj3 (x:ex2 P Q) : Q (ex_proj1 (ex_of_ex2 x)) :=
    match x with ex_intro2 _ _ _ _ b => b end.

End ex2_Projections.

Definition all (A:Type) (P:A -> Prop) := forall x:A, P x.
Register all as core.all.

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
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

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ y _ : rename.
Arguments eq_rec [A] x P _ y _ : rename.
Arguments eq_rect [A] x P _ y _ : rename.

Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

#[global]
Hint Resolve I conj or_introl or_intror : core.
#[global]
Hint Resolve eq_refl: core.
#[global]
Hint Resolve ex_intro ex_intro2: core.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

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

    Register eq_sym as core.eq.sym.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Register eq_trans as core.eq.trans.

    Theorem eq_trans_r : x = y -> z = y -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Register f_equal as core.eq.congr.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

  End equality.

  Definition eq_sind_r :
    forall (A:Type) (x:A) (P:A -> SProp), P x -> forall y:A, y = x -> P y.
  Proof.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Register eq_ind_r as core.eq.ind_r.

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

  Notation "'rew' 'dependent' H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (match eq_sym H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.

Import EqNotations.

Section equality_dep.
  Variable A : Type.
  Variable B : A -> Type.
  Variable f : forall x, B x.
  Variables x y : A.

  Theorem f_equal_dep (H: x = y) : rew H in f x = f y.
  Proof.
    destruct H; reflexivity.
  Defined.

End equality_dep.

Lemma f_equal_dep2 {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a))
  {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2) :
  rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
Proof.
  destruct H, 1. reflexivity.
Defined.

Lemma rew_opp_r A (P:A->Type) (x y:A) (H:x=y) (a:P y) : rew H in rew <- H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Lemma rew_opp_l A (P:A->Type) (x y:A) (H:x=y) (a:P x) : rew <- H in rew H in a = a.
Proof.
destruct H.
reflexivity.
Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Register f_equal2 as core.eq.congr2.

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

Theorem f_equal_compose A B C (a b:A) (f:A->B) (g:B->C) (e:a=b) :
  f_equal g (f_equal f e) = f_equal (fun a => g (f a)) e.
Proof.
  destruct e. reflexivity.
Defined.

(** The groupoid structure of equality *)

Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_trans_refl_r A (x y:A) (e:x=y) : eq_trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Defined.

Theorem eq_sym_involutive A (x y:A) (e:x=y) : eq_sym (eq_sym e) = e.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_l A (x y:A) (e:x=y) : eq_trans (eq_sym e) e = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_sym_inv_r A (x y:A) (e:x=y) : eq_trans e (eq_sym e) = eq_refl.
Proof.
  destruct e; reflexivity.
Defined.

Theorem eq_trans_assoc A (x y z t:A) (e:x=y) (e':y=z) (e'':z=t) :
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  destruct e''; reflexivity.
Defined.

Theorem rew_map A B (P:B->Type) (f:A->B) x1 x2 (H:x1=x2) (y:P (f x1)) :
  rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  destruct H; reflexivity.
Defined.

Theorem eq_trans_map {A B} {x1 x2 x3:A} {y1:B x1} {y2:B x2} {y3:B x3}
  (H1:x1=x2) (H2:x2=x3) (H1': rew H1 in y1 = y2) (H2': rew H2 in y2 = y3) :
  rew eq_trans H1 H2 in y1 = y3.
Proof.
  destruct H2. exact (eq_trans H1' H2').
Defined.

Lemma map_subst {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H:x=y) (z:P x) :
  rew H in f x z = f y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma map_subst_map {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x))
  {x y} (H:x=y) (z:P x) :
  rew f_equal f H in g x z = g y (rew H in z).
Proof.
  destruct H. reflexivity.
Defined.

Lemma rew_swap A (P:A->Type) x1 x2 (H:x1=x2) (y1:P x1) (y2:P x2) : rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof.
  destruct H. trivial.
Defined.

Lemma rew_compose A (P:A->Type) x1 x2 x3 (H1:x1=x2) (H2:x2=x3) (y:P x1) :
  rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  destruct H2. reflexivity.
Defined.

(** Extra properties of equality *)

Theorem eq_id_comm_l A (f:A->A) (Hf:forall a, a = f a) a : f_equal f (Hf a) = Hf (f a).
Proof.
  unfold f_equal.
  rewrite <- (eq_trans_sym_inv_l (Hf a)).
  destruct (Hf a) at 1 2.
  destruct (Hf a).
  reflexivity.
Defined.

Theorem eq_id_comm_r A (f:A->A) (Hf:forall a, f a = a) a : f_equal f (Hf a) = Hf (f a).
Proof.
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

Lemma eq_refl_map_distr A B x (f:A->B) : f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  reflexivity.
Qed.

Lemma eq_trans_map_distr A B x y z (f:A->B) (e:x=y) (e':y=z) : f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
destruct e'.
reflexivity.
Defined.

Lemma eq_sym_map_distr A B (x y:A) (f:A->B) (e:x=y) : eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
destruct e.
reflexivity.
Defined.

Lemma eq_trans_sym_distr A (x y z:A) (e:x=y) (e':y=z) : eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
destruct e, e'.
reflexivity.
Defined.

Lemma eq_trans_rew_distr A (P:A -> Type) (x y z:A) (e:x=y) (e':y=z) (k:P x) :
    rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  destruct e, e'; reflexivity.
Qed.

Lemma rew_const A P (x y:A) (e:x=y) (k:P) :
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

#[global]
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
      * symmetry; auto.
      * auto.
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
  destruct (H P) as ((x & Hx & _),_); [trivial|].
  exists x. split; [trivial|].
  destruct (H (fun x'=>x=x')) as (_,Huniq).
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

#[global]
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

(** More properties of [ex] and [ex2] that rely on equality being present *)

(** We define restricted versions of [ex_rect] and [ex_rec] which
    allow elimination into non-Prop sorts when the inductive is not
    informative *)

(** η Principles *)
Definition ex_eta {A : Prop} {P} (p : exists a : A, P a)
  : p = ex_intro _ (ex_proj1 p) (ex_proj2 p).
Proof. destruct p; reflexivity. Defined.

Definition ex2_eta {A : Prop} {P Q} (p : exists2 a : A, P a & Q a)
  : p = ex_intro2 _ _ (ex_proj1 (ex_of_ex2 p)) (ex_proj2 (ex_of_ex2 p)) (ex_proj3 p).
Proof. destruct p; reflexivity. Defined.

Section ex_Prop.
  Variables (A:Prop) (P:A->Prop).

  Definition ex_rect (P0 : ex P -> Type) (f : forall x p, P0 (ex_intro P x p))
    : forall e, P0 e
    := fun e => rew <- ex_eta e in f _ _.
  Definition ex_rec : forall (P0 : ex P -> Set) (f : forall x p, P0 (ex_intro P x p)),
      forall e, P0 e
    := ex_rect.

End ex_Prop.

(** Equality for [ex] *)
Section ex.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition ex_proj1_eq {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v)
    : ex_proj1 u = ex_proj1 v
    := f_equal (@ex_proj1 _ _) p.

  (** Projecting an equality of a pair to equality of the second components *)
  Definition ex_proj2_eq {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v)
    : rew ex_proj1_eq p in ex_proj2 u = ex_proj2 v
    := rew dependent p in eq_refl.

  (** Equality of [ex] is itself a [ex] (forwards-reasoning version) *)
  Definition eq_ex_intro_uncurried {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : exists p : u1 = v1, rew p in u2 = v2)
    : ex_intro _ u1 u2 = ex_intro _ v1 v2.
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** Equality of [ex] is itself a [ex] (backwards-reasoning version) *)
  Definition eq_ex_uncurried {A : Prop} {P : A -> Prop} (u v : exists a : A, P a)
             (pq : exists p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v)
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    apply eq_ex_intro_uncurried; exact pq.
  Defined.

  (** Curried version of proving equality of [ex] types *)
  Definition eq_ex_intro {A : Type} {P : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1) (q : rew p in u2 = v2)
    : ex_intro _ u1 u2 = ex_intro _ v1 v2
    := eq_ex_intro_uncurried (ex_intro _ p q).

  (** Curried version of proving equality of [ex] types *)
  Definition eq_ex {A : Prop} {P : A -> Prop} (u v : exists a : A, P a)
             (p : ex_proj1 u = ex_proj1 v) (q : rew p in ex_proj2 u = ex_proj2 v)
    : u = v
    := eq_ex_uncurried u v (ex_intro _ p q).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_ex_intro_l {A : Prop} {P : A -> Prop} u1 u2 (v : exists a : A, P a)
             (p : u1 = ex_proj1 v) (q : rew p in u2 = ex_proj2 v)
    : ex_intro P u1 u2 = v
    := eq_ex (ex_intro P u1 u2) v p q.
  Definition eq_ex_intro_r {A : Prop} {P : A -> Prop} (u : exists a : A, P a) v1 v2
             (p : ex_proj1 u = v1) (q : rew p in ex_proj2 u = v2)
    : u = ex_intro P v1 v2
    := eq_ex u (ex_intro P v1 v2) p q.

  (** Induction principle for [@eq (ex _)] *)
  Definition eq_ex_eta {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (p : u = v) : p = eq_ex u v (ex_proj1_eq p) (ex_proj2_eq p).
  Proof. destruct p, u; reflexivity. Defined.
  Definition eq_ex_rect {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (Q : u = v -> Type)
             (f : forall p q, Q (eq_ex u v p q))
    : forall p, Q p
    := fun p => rew <- eq_ex_eta p in f _ _.
  Definition eq_ex_rec {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Set) := eq_ex_rect Q.
  Definition eq_ex_ind {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Prop) := eq_ex_rec Q.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_ex_rect_ex_intro_l {A : Prop} {P : A -> Prop} {u1 u2 v} (Q : _ -> Type)
             (f : forall p q, Q (eq_ex_intro_l (P:=P) u1 u2 v p q))
    : forall p, Q p
    := eq_ex_rect Q f.
  Definition eq_ex_rect_ex_intro_r {A : Prop} {P : A -> Prop} {u v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (eq_ex_intro_r (P:=P) u v1 v2 p q))
    : forall p, Q p
    := eq_ex_rect Q f.
  Definition eq_ex_rect_ex_intro {A : Prop} {P : A -> Prop} {u1 u2 v1 v2} (Q : _ -> Type)
             (f : forall p q, Q (@eq_ex_intro A P u1 v1 u2 v2 p q))
    : forall p, Q p
    := eq_ex_rect Q f.

  Definition eq_ex_rect_uncurried {A : Prop} {P : A -> Prop} {u v : exists a : A, P a} (Q : u = v -> Type)
             (f : forall pq, Q (eq_ex u v (ex_proj1 pq) (ex_proj2 pq)))
    : forall p, Q p
    := eq_ex_rect Q (fun p q => f (ex_intro _ p q)).
  Definition eq_ex_rec_uncurried {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Set) := eq_ex_rect_uncurried Q.
  Definition eq_ex_ind_uncurried {A : Prop} {P : A -> Prop} {u v} (Q : u = v :> (exists a : A, P a) -> Prop) := eq_ex_rec_uncurried Q.

  (** Equality of [ex] when the property is an hProp *)
  Definition eq_ex_hprop {A : Prop} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : exists a : A, P a)
             (p : ex_proj1 u = ex_proj1 v)
    : u = v
    := eq_ex u v p (P_hprop _ _ _).

  Definition eq_ex_intro_hprop {A : Type} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (p : u1 = v1)
    : ex_intro P u1 u2 = ex_intro P v1 v2
    := eq_ex_intro p (P_hprop _ _ _).

  (** Equivalence of equality of [ex] with a [ex] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_ex_uncurried_iff {A : Prop} {P : A -> Prop} (u v : exists a : A, P a)
    : u = v <-> exists p : ex_proj1 u = ex_proj1 v, rew p in ex_proj2 u = ex_proj2 v.
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_ex_uncurried ].
  Defined.

  (** Equivalence of equality of [ex] involving hProps with equality of the first components *)
  Definition eq_ex_hprop_iff {A : Prop} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : exists a : A, P a)
    : u = v <-> (ex_proj1 u = ex_proj1 v)
    := conj (fun p => f_equal (@ex_proj1 _ _) p) (eq_ex_hprop P_hprop u v).

  Lemma rew_ex {A' : Type} {x} {P : A' -> Prop} (Q : forall a, P a -> Prop) (u : exists p : P x, Q x p) {y} (H : x = y)
    : rew [fun a => exists p : P a, Q a p] H in u
      = ex_intro
          (Q y)
          (rew H in ex_proj1 u)
          (rew dependent H in ex_proj2 u).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End ex.
Global Arguments eq_ex_intro A P _ _ _ _ !p !q / .

Section ex2_Prop.
  Variables (A:Prop) (P Q:A->Prop).

  Definition ex2_rect (P0 : ex2 P Q -> Type) (f : forall x p q, P0 (ex_intro2 P Q x p q))
    : forall e, P0 e
    := fun e => rew <- ex2_eta e in f _ _ _.
  Definition ex2_rec : forall (P0 : ex2 P Q -> Set) (f : forall x p q, P0 (ex_intro2 P Q x p q)),
      forall e, P0 e
    := ex2_rect.

End ex2_Prop.

(** Equality for [ex2] *)
Section ex2.
  (* We make [ex_of_ex2] a coercion so we can use [proj1], [proj2] on [ex2] *)
  Local Coercion ex_of_ex2 : ex2 >-> ex.
  Local Unset Implicit Arguments.
  (** Projecting an equality of a pair to equality of the first components *)
  Definition ex_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v)
    : u = v :> exists a : A, P a
    := f_equal _ p.
  Definition ex_proj1_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v)
    : ex_proj1 u = ex_proj1 v
    := ex_proj1_eq (ex_of_ex2_eq p).

  (** Projecting an equality of a pair to equality of the second components *)
  Definition ex_proj2_of_ex2_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v)
    : rew ex_proj1_of_ex2_eq p in ex_proj2 u = ex_proj2 v
    := rew dependent p in eq_refl.

  (** Projecting an equality of a pair to equality of the third components *)
  Definition ex_proj3_eq {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v)
    : rew ex_proj1_of_ex2_eq p in ex_proj3 u = ex_proj3 v
    := rew dependent p in eq_refl.

  (** Equality of [ex2] is itself a [ex2] (fowards-reasoning version) *)
  Definition eq_ex_intro2_uncurried {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (pqr : exists2 p : u1 = v1, rew p in u2 = v2 & rew p in u3 = v3)
    : ex_intro2 _ _ u1 u2 u3 = ex_intro2 _ _ v1 v2 v3.
  Proof.
    destruct pqr as [p q r].
    destruct r, q, p; simpl.
    reflexivity.
  Defined.

  (** Equality of [ex2] is itself a [ex2] (backwards-reasoning version) *)
  Definition eq_ex2_uncurried {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a)
             (pqr : exists2 p : ex_proj1 u = ex_proj1 v,
                                rew p in ex_proj2 u = ex_proj2 v & rew p in ex_proj3 u = ex_proj3 v)
    : u = v.
  Proof.
    destruct u as [u1 u2 u3], v as [v1 v2 v3]; simpl in *.
    apply eq_ex_intro2_uncurried; exact pqr.
  Defined.

  (** Curried version of proving equality of [ex] types *)
  Definition eq_ex2 {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a)
             (p : ex_proj1 u = ex_proj1 v)
             (q : rew p in ex_proj2 u = ex_proj2 v)
             (r : rew p in ex_proj3 u = ex_proj3 v)
    : u = v
    := eq_ex2_uncurried u v (ex_intro2 _ _ p q r).

  Definition eq_ex_intro2 {A : Type} {P Q : A -> Prop} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (p : u1 = v1)
             (q : rew p in u2 = v2)
             (r : rew p in u3 = v3)
    : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3
    := eq_ex_intro2_uncurried (ex_intro2 _ _ p q r).

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_ex_intro2_l {A : Prop} {P Q : A -> Prop} u1 u2 u3 (v : exists2 a : A, P a & Q a)
             (p : u1 = ex_proj1 v) (q : rew p in u2 = ex_proj2 v) (r : rew p in u3 = ex_proj3 v)
    : ex_intro2 P Q u1 u2 u3 = v
    := eq_ex2 (ex_intro2 P Q u1 u2 u3) v p q r.
  Definition eq_ex_intro2_r {A : Prop} {P Q : A -> Prop} (u : exists2 a : A, P a & Q a) v1 v2 v3
             (p : ex_proj1 u = v1) (q : rew p in ex_proj2 u = v2) (r : rew p in ex_proj3 u = v3)
    : u = ex_intro2 P Q v1 v2 v3
    := eq_ex2 u (ex_intro2 P Q v1 v2 v3) p q r.

  (** Equality of [ex2] when the second property is an hProp *)
  Definition eq_ex2_hprop {A : Prop} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : exists2 a : A, P a & Q a)
             (p : u = v :> exists a : A, P a)
    : u = v
    := eq_ex2 u v (ex_proj1_eq p) (ex_proj2_eq p) (Q_hprop _ _ _).

  Definition eq_ex_intro2_hprop_nondep {A : Type} {P : A -> Prop} {Q : Prop} (Q_hprop : forall (p q : Q), p = q)
             {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 v3 : Q}
             (p : ex_intro _ u1 u2 = ex_intro _ v1 v2)
    : ex_intro2 _ _ u1 u2 u3 = ex_intro2 _ _ v1 v2 v3
    := rew [fun v3 => _ = ex_intro2 _ _ _ _ v3] (Q_hprop u3 v3) in
        f_equal (fun u => match u with ex_intro _ u1 u2 => ex_intro2 _ _ u1 u2 u3 end) p.

  Definition eq_ex_intro2_hprop {A : Type} {P Q : A -> Prop}
             (P_hprop : forall x (p q : P x), p = q)
             (Q_hprop : forall x (p q : Q x), p = q)
             {u1 v1 : A} {u2 : P u1} {v2 : P v1} {u3 : Q u1} {v3 : Q v1}
             (p : u1 = v1)
    : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3
    := eq_ex_intro2 p (P_hprop _ _ _) (Q_hprop _ _ _).

  (** Equivalence of equality of [ex2] with a [ex2] of equality *)
  (** We could actually prove an isomorphism here, and not just [<->],
      but for simplicity, we don't. *)
  Definition eq_ex2_uncurried_iff {A : Prop} {P Q : A -> Prop} (u v : exists2 a : A, P a & Q a)
    : u = v
      <-> exists2 p : ex_proj1 u = ex_proj1 v,
                      rew p in ex_proj2 u = ex_proj2 v & rew p in ex_proj3 u = ex_proj3 v.
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply eq_ex2_uncurried ].
  Defined.

  (** Induction principle for [@eq (ex2 _ _)] *)
  Definition eq_ex2_eta {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (p : u = v)
    : p = eq_ex2 u v (ex_proj1_of_ex2_eq p) (ex_proj2_of_ex2_eq p) (ex_proj3_eq p).
  Proof. destruct p, u; reflexivity. Defined.
  Definition eq_ex2_rect {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (R : u = v -> Type)
             (f : forall p q r, R (eq_ex2 u v p q r))
    : forall p, R p
    := fun p => rew <- eq_ex2_eta p in f _ _ _.
  Definition eq_ex2_rec {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Set) := eq_ex2_rect R.
  Definition eq_ex2_ind {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Prop) := eq_ex2_rec R.

  (** In order to have a performant [inversion_sigma], we define
      specialized versions for when we have constructors on one or
      both sides of the equality *)
  Definition eq_ex2_rect_ex_intro2_l {A : Prop} {P Q : A -> Prop} {u1 u2 u3 v} (R : _ -> Type)
             (f : forall p q r, R (eq_ex_intro2_l (P:=P) (Q:=Q) u1 u2 u3 v p q r))
    : forall p, R p
    := eq_ex2_rect R f.
  Definition eq_ex2_rect_ex_intro2_r {A : Prop} {P Q : A -> Prop} {u v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (eq_ex_intro2_r (P:=P) (Q:=Q) u v1 v2 v3 p q r))
    : forall p, R p
    := eq_ex2_rect R f.
  Definition eq_ex2_rect_ex_intro2 {A : Prop} {P Q : A -> Prop} {u1 u2 u3 v1 v2 v3} (R : _ -> Type)
             (f : forall p q r, R (@eq_ex_intro2 A P Q u1 v1 u2 v2 u3 v3 p q r))
    : forall p, R p
    := eq_ex2_rect R f.

  Definition eq_ex2_rect_uncurried {A : Prop} {P Q : A -> Prop} {u v : exists2 a : A, P a & Q a} (R : u = v -> Type)
             (f : forall pqr : exists2 p : _ = _, _ & _, R (eq_ex2 u v (ex_proj1 pqr) (ex_proj2 pqr) (ex_proj3 pqr)))
    : forall p, R p
    := eq_ex2_rect R (fun p q r => f (ex_intro2 _ _ p q r)).
  Definition eq_ex2_rec_uncurried {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Set) := eq_ex2_rect_uncurried R.
  Definition eq_ex2_ind_uncurried {A : Prop} {P Q : A -> Prop} {u v} (R : u = v :> (exists2 a : A, P a & Q a) -> Prop) := eq_ex2_rec_uncurried R.

  (** Equivalence of equality of [ex2] involving hProps with equality of the first components *)
  Definition eq_ex2_hprop_iff {A : Prop} {P Q : A -> Prop} (Q_hprop : forall (x : A) (p q : Q x), p = q)
             (u v : exists2 a : A, P a & Q a)
    : u = v <-> (u = v :> exists a : A, P a)
    := conj (fun p => f_equal (@ex_of_ex2 _ _ _) p) (eq_ex2_hprop Q_hprop u v).

  (** Non-dependent classification of equality of [ex] *)
  Definition eq_ex2_nondep {A : Prop} {B C : Prop} (u v : @ex2 A (fun _ => B) (fun _ => C))
             (p : ex_proj1 u = ex_proj1 v) (q : ex_proj2 u = ex_proj2 v) (r : ex_proj3 u = ex_proj3 v)
    : u = v
    := @eq_ex2 _ _ _ u v p (eq_trans (rew_const _ _) q) (eq_trans (rew_const _ _) r).

  (** Classification of transporting across an equality of [ex2]s *)
  Lemma rew_ex2 {A' : Type} {x} {P : A' -> Prop} (Q R : forall a, P a -> Prop)
        (u : exists2 p : P x, Q x p & R x p)
        {y} (H : x = y)
    : rew [fun a => exists2 p : P a, Q a p & R a p] H in u
      = ex_intro2
          (Q y)
          (R y)
          (rew H in ex_proj1 u)
          (rew dependent H in ex_proj2 u)
          (rew dependent H in ex_proj3 u).
  Proof.
    destruct H, u; reflexivity.
  Defined.
End ex2.
Global Arguments eq_ex_intro2 A P Q _ _ _ _ _ _ !p !q !r / .
