Require Import Coq.Program.Utils.
Require Import Coq.Program.Wf.

(** The converse of functional equality. *)

Lemma equal_f : forall A B : Type, forall (f g : A -> B), 
  f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

(** Statements of functional equality for simple and dependent functions. *)

Axiom fun_extensionality : forall A B (f g : A -> B), 
  (forall x, f x = g x) -> f = g.

Axiom fun_extensionality_dep : forall A, forall B : (A -> Type), forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.

Hint Resolve fun_extensionality fun_extensionality_dep : program.

(** The two following lemmas allow to unfold a well-founded fixpoint definition without
   restriction using the functional extensionality axiom. *)

(** For a function defined with Program using a well-founded order. *)

Lemma fix_sub_eq_ext :
  forall (A : Set) (R : A -> A -> Prop) (Rwf : well_founded R)
    (P : A -> Set)
    (F_sub : forall x : A, (forall  {y : A | R y x}, P (`y)) -> P x),
    forall x : A,
      Fix_sub A R Rwf P F_sub x =
        F_sub x (fun {y : A | R y x}=> Fix A R Rwf P F_sub (`y)).
Proof.
  intros ; apply Fix_eq ; auto.
  intros.
  assert(f = g).
  apply (fun_extensionality_dep _ _ _ _ H).
  rewrite H0 ; auto.
Qed.

(** For a function defined with Program using a measure. *)

Lemma fix_sub_measure_eq_ext :
  forall (A : Type) (f : A -> nat) (P : A -> Type)
    (F_sub : forall x : A, (forall  {y : A | f y < f x}, P (`y)) -> P x),
    forall x : A,
      Fix_measure_sub A f P F_sub x =
        F_sub x (fun {y : A | f y < f x}=> Fix_measure_sub A f P F_sub (`y)).
Proof.
  intros ; apply Fix_measure_eq ; auto.
  intros.
  assert(f0 = g).
  apply (fun_extensionality_dep _ _ _ _ H).
  rewrite H0 ; auto.
Qed.

Ltac apply_ext :=
  match goal with 
    [ |- ?x = ?y ] => apply (@fun_extensionality _ _ x y)
  end.


