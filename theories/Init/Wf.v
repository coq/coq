(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * This module proves the validity of
    - well-founded recursion (also known as course of values)
    - well-founded induction
    from a well-founded ordering on a given set *)

Set Implicit Arguments.

Require Import Notations.
Require Import Ltac.
Require Import Logic.
Require Import Datatypes.
Require Import Specif.

(** Well-founded induction principle on [Prop] *)

Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)
 (** (Acc_rect is automatically defined because Acc is a singleton type) *)

 Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

 Register Acc as core.wf.acc.

 Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.
  destruct 1; trivial.
 Defined.

 Global Arguments Acc_inv [x] _ [y] _, [x] _ y _.
 Register Acc_inv as core.wf.acc_inv.

 (** A relation is well-founded if every element is accessible *)

 Definition well_founded := forall a:A, Acc a.

 Register well_founded as core.wf.well_founded.

 (** Well-founded induction on [Set] and [Prop] *)

 Hypothesis Rwf : well_founded.

 Theorem well_founded_induction_type :
  forall P:A -> Type,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  intros; apply Acc_rect; auto.
 Defined.

 Theorem well_founded_induction :
  forall P:A -> Set,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Set => well_founded_induction_type P).
 Defined.

 Theorem well_founded_ind :
  forall P:A -> Prop,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Prop => well_founded_induction_type P).
 Defined.

(** Well-founded fixpoints *)

 Section FixPoint.

  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

  Fixpoint Fix_F (x:A) (a:Acc x) : P x :=
    F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).

  Scheme Acc_inv_dep := Induction for Acc Sort Prop.

  Lemma Fix_F_eq (x:A) (r:Acc x) :
     F (fun (y:A) (p:R y x) => Fix_F (x:=y) (Acc_inv r p)) = Fix_F (x:=x) r.
  Proof.
   destruct r using Acc_inv_dep; auto.
  Qed.

  Definition Fix (x:A) := Fix_F (Rwf x).

  (** Proof that [well_founded_induction] satisfies the fixpoint equation.
      It requires an extra property of the functional *)

  Hypothesis
    F_ext :
      forall (x:A) (f g:forall y:A, R y x -> P y),
        (forall (y:A) (p:R y x), f y p = g y p) -> F f = F g.

  Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F r = Fix_F s.
  Proof.
   intro x; induction (Rwf x); intros r s.
   rewrite <- (Fix_F_eq r); rewrite <- (Fix_F_eq s); intros.
   apply F_ext; auto.
  Qed.

  Lemma Fix_eq : forall x:A, Fix x = F (fun (y:A) (p:R y x) => Fix y).
  Proof.
   intro x; unfold Fix.
   rewrite <- Fix_F_eq.
   apply F_ext; intros.
   apply Fix_F_inv.
  Qed.

 End FixPoint.

End Well_founded.

(** Well-founded fixpoints over pairs *)

Section Well_founded_2.

  Variables A B : Type.
  Variable R : A * B -> A * B -> Prop.

  Variable P : A -> B -> Type.

  Section FixPoint_2.

  Variable
    F :
      forall (x:A) (x':B),
        (forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x'.

  Fixpoint Fix_F_2 (x:A) (x':B) (a:Acc R (x, x')) : P x x' :=
    F
      (fun (y:A) (y':B) (h:R (y, y') (x, x')) =>
         Fix_F_2 (x:=y) (x':=y') (Acc_inv a (y,y') h)).

  End FixPoint_2.

  Hypothesis Rwf : well_founded R.

  Theorem well_founded_induction_type_2 :
   (forall (x:A) (x':B),
      (forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x') ->
   forall (a:A) (b:B), P a b.
  Proof.
   intros; apply Fix_F_2; auto.
  Defined.

End Well_founded_2.

Notation Acc_iter   := Fix_F   (only parsing). (* compatibility *)
Notation Acc_iter_2 := Fix_F_2 (only parsing). (* compatibility *)



(* Added by Julien Forest on 13/11/20

This construction is originally by Georges Gonthier, see
https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00013.html *)

Section Acc_generator.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  (* *Lazily* add 2^n - 1 Acc_intro on top of wf. 
     Needed for fast reductions using Function and Program Fixpoint 
     and probably using Fix and Fix_F_2 
   *)    
  Fixpoint Acc_intro_generator n (wf : well_founded R)  := 
    match n with 
        | O => wf
        | S n => fun x => Acc_intro x (fun y _ => Acc_intro_generator n (Acc_intro_generator n wf) y)
    end.


End Acc_generator.

Unset Implicit Arguments.

Local Notation " `  t " := (proj1_sig t) (at level 10, t at next level).

Section Well_founded.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.

  Variable P : A -> Type.

  Variable F_sub : forall x:A, (forall y: { y : A | R y x }, P (proj1_sig y)) -> P x.

  Fixpoint Fix_F_sub (x : A) (r : Acc R x) : P x :=
    F_sub x (fun y: { y : A | R y x}  => Fix_F_sub (proj1_sig y)
      (Acc_inv r (proj2_sig y))).

  Definition Fix_sub (x : A) := Fix_F_sub x (Rwf x).

  Register Fix_sub as program.wf.fix_sub.

  (* Notation Fix_F := (Fix_F_sub P F_sub) (only parsing). (* alias *) *)
  (* Definition Fix (x:A) := Fix_F_sub P F_sub x (Rwf x). *)

  Hypothesis F_ext :
    forall (x:A) (f g:forall y:{y:A | R y x}, P (proj1_sig y)),
      (forall y:{y : A | R y x}, f y = g y) -> F_sub x f = F_sub x g.

  Lemma Fix_F_sub_eq :
    forall (x:A) (r:Acc R x),
      F_sub x (fun y:{y:A | R y x} => Fix_F_sub (proj1_sig y) (Acc_inv r (proj2_sig y))) = Fix_F_sub x r.
  Proof.
    intros x r; destruct r using Acc_inv_dep; auto.
  Qed.

  Lemma Fix_F_sub_inv : forall (x:A) (r s:Acc R x), Fix_F_sub x r = Fix_F_sub x s.
  Proof.
    intro x; induction (Rwf x); intros.
    rewrite <- 2 Fix_F_sub_eq; intros. apply F_ext; intros []; auto.
  Qed.

  Lemma Fix_sub_eq : forall x:A, Fix_sub x = F_sub x (fun y:{ y:A | R y x} => Fix_sub (proj1_sig y)).
  Proof.
    intro x; unfold Fix_sub.
    rewrite <- (Fix_F_sub_eq ).
    apply F_ext; intros.
    apply Fix_F_sub_inv.
  Qed.

  Lemma fix_sub_eq :
    forall x : A,
      Fix_sub x =
      let f_sub := F_sub in
        f_sub x (fun y: {y : A | R y x} => Fix_sub (proj1_sig y)).
  Proof.
    exact Fix_sub_eq.
  Qed.

End Well_founded.

Set Implicit Arguments.

(** Reasoning about well-founded fixpoints on measures. *)

Section Measure_well_founded.

  (* Measure relations are well-founded if the underlying relation is well-founded. *)

  Variables T M: Type.
  Variable R: M -> M -> Prop.
  Hypothesis wf: well_founded R.
  Variable m: T -> M.

  Definition MR (x y: T): Prop := R (m x) (m y).

  Register MR as program.wf.mr.

  Lemma measure_wf: well_founded MR.
  Proof with auto.
    unfold well_founded.
    cut (forall (a: M) (a0: T), m a0 = a -> Acc MR a0).
    + intros H a.
      apply (H (m a))...
    + apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc MR a)).
      intros ? H ? H0.
      apply Acc_intro.
      intros y H1.
      unfold MR in H1.
      rewrite H0 in H1.
      apply (H (m y))...
  Defined.

End Measure_well_founded.

#[global]
Hint Resolve measure_wf : core.

Section Fix_rects.

  Variable A: Type.
  Variable P: A -> Type.
  Variable R : A -> A -> Prop.
  Variable Rwf : well_founded R.
  Variable f: forall (x : A), (forall y: { y: A | R y x }, P (proj1_sig y)) -> P x.

  Lemma F_unfold x r:
    Fix_F_sub A R P f x r =
    f (fun y => Fix_F_sub A R P f (proj1_sig y) (Acc_inv r (proj2_sig y))).
  Proof. intros. case r; auto. Qed.

  (* Fix_F_sub_rect lets one prove a property of
  functions defined using Fix_F_sub by showing
  that property to be invariant over single application of the
  function body (f in our case). *)

  Lemma Fix_F_sub_rect
    (Q: forall x, P x -> Type)
    (inv: forall x: A,
     (forall (y: A) (H: R y x) (a: Acc R y),
        Q y (Fix_F_sub A R P f y a)) ->
        forall (a: Acc R x),
          Q x (f (fun y: {y: A | R y x} =>
            Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y)))))
    : forall x a, Q _ (Fix_F_sub A R P f x a).
  Proof with auto.
    set (R' := fun (x: A) => forall a, Q _ (Fix_F_sub A R P f x a)).
    cut (forall x, R' x)...
    apply (well_founded_induction_type Rwf).
    subst R'.
    simpl.
    intros.
    rewrite F_unfold...
  Qed.

  (* Let's call f's second parameter its "lowers" function, since it
  provides it access to results for inputs with a lower measure.

  In preparation of lemma similar to Fix_F_sub_rect, but
  for Fix_sub, we first
  need an extra hypothesis stating that the function body has the
  same result for different "lowers" functions (g and h below) as long
  as those produce the same results for lower inputs, regardless
  of the lt proofs. *)

  Hypothesis equiv_lowers:
    forall x0 (g h: forall x: {y: A | R y x0}, P (proj1_sig x)),
    (forall x p p', g (exist (fun y: A => R y x0) x p) = h (exist (*FIXME shouldn't be needed *) (fun y => R y x0) x p')) ->
      f g = f h.

  (* From equiv_lowers, it follows that
   [Fix_F_sub A R P f x] applications do not not
  depend on the Acc proofs. *)

  Lemma eq_Fix_F_sub x (a a': Acc R x):
    Fix_F_sub A R P f x a =
    Fix_F_sub A R P f x a'.
  Proof.
    revert a'.
    pattern x, (Fix_F_sub A R P f x a).
    apply Fix_F_sub_rect.
    intros ? H **.
    rewrite F_unfold.
    apply equiv_lowers.
    intros.
    apply H.
    assumption.
  Qed.

  (* Finally, Fix_F_rect lets one prove a property of
  functions defined using Fix_F_sub by showing that
  property to be invariant over single application of the function
  body (f). *)

  Lemma Fix_sub_rect
    (Q: forall x, P x -> Type)
    (inv: forall
      (x: A)
      (H: forall (y: A), R y x -> Q y (Fix_sub A R Rwf P f y))
      (a: Acc R x),
        Q x (f (fun y: {y: A | R y x} => Fix_sub A R Rwf P f (proj1_sig y))))
    : forall x, Q _ (Fix_sub A R Rwf P f x).
  Proof with auto.
    unfold Fix_sub.
    intros x.
    apply Fix_F_sub_rect.
    intros x0 H a.
    assert (forall y: A, R y x0 -> Q y (Fix_F_sub A R P f y (Rwf y))) as X0...
    set (q := inv x0 X0 a). clearbody q.
    rewrite <- (equiv_lowers (fun y: {y: A | R y x0} =>
      Fix_F_sub A R P f (proj1_sig y) (Rwf (proj1_sig y)))
    (fun y: {y: A | R y x0} => Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y))))...
    intros.
    apply eq_Fix_F_sub.
  Qed.

End Fix_rects.

(** Tactic to fold a definition based on [Fix_measure_sub]. *)

Ltac fold_sub f :=
  match goal with
    | [ |- ?T ] =>
      match T with
        context C [ @Fix_sub _ _ _ _ _ ?arg ] =>
        let app := context C [ f arg ] in
          change app
      end
  end.
