(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Standard functions and proofs about them.
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Program.FunctionalExtensionality.

Notation  " 'λ' x : T , y " := (fun x:T => y) (at level 100, x,T,y at level 10, no associativity) : program_scope.

Open Scope program_scope.

Definition id `A` := λ x : A, x.

Definition compose `A B C` (g : B -> C) (f : A -> B) := λ x : A , g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)  (at level 50, left associativity) : program_scope.

Lemma compose_id_left : forall A B (f : A -> B), id ∘ f = f.
Proof.
  intros.
  unfold id, compose.
  symmetry ; apply eta_expansion.
Qed.

Lemma compose_id_right : forall A B (f : A -> B), f ∘ id = f.
Proof.
  intros.
  unfold id, compose.
  symmetry ; apply eta_expansion.
Qed.

Lemma compose_assoc : forall A B C D (f : A -> B) (g : B -> C) (h : C -> D), 
  h ∘ g ∘ f = h ∘ (g ∘ f).
Proof.
  intros.
  reflexivity.
Qed.

Hint Rewrite @compose_id_left @compose_id_right @compose_assoc : core.

Definition arrow (A B : Type) := A -> B.

Definition impl (A B : Prop) : Prop := A -> B.

Notation " f '#' x " := (f x) (at level 100, x at level 200, only parsing).

Definition const `A B` (a : A) := fun x : B => a.

Definition flip `A B C` (f : A -> B -> C) x y := f y x.

Lemma flip_flip : forall A B C (f : A -> B -> C), flip (flip f) = f.
Proof.
  unfold flip.
  intros.
  extensionality x ; extensionality y.
  reflexivity.
Qed.

Definition apply `A B` (f : A -> B) (x : A) := f x.

(** Notations for the unit type and value. *)

Notation " () " := Datatypes.unit : type_scope.
Notation " () " := tt.

(** Set maximally inserted implicit arguments for standard definitions. *)

Implicit Arguments eq [[A]].

Implicit Arguments Some [[A]].
Implicit Arguments None [[A]].

Implicit Arguments inl [[A] [B]].
Implicit Arguments inr [[A] [B]].

Implicit Arguments left [[A] [B]].
Implicit Arguments right [[A] [B]].

(** Curryfication. *)

Definition curry `a b c` (f : a -> b -> c) (p : prod a b) : c :=
  let (x, y) := p in f x y.

Definition uncurry `a b c` (f : prod a b -> c) (x : a) (y : b) : c :=
  f (x, y).

Lemma uncurry_curry : forall a b c (f : a -> b -> c), uncurry (curry f) = f.
Proof.
  simpl ; intros.
  unfold uncurry, curry.
  extensionality x ; extensionality y.
  reflexivity.
Qed.

Lemma curry_uncurry : forall a b c (f : prod a b -> c), curry (uncurry f) = f.
Proof.
  simpl ; intros.
  unfold uncurry, curry.
  extensionality x. 
  destruct x ; simpl ; reflexivity.
Qed.

(** Useful implicits and notations for lists. *)

Require Import Coq.Lists.List.

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].

Notation " [] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

(** n-ary exists ! *)

Notation " 'exists' x y , p" := (ex (fun x => (ex (fun y => p))))
  (at level 200, x ident, y ident, right associativity) : type_scope.

Notation " 'exists' x y z , p" := (ex (fun x => (ex (fun y => (ex (fun z => p))))))
  (at level 200, x ident, y ident, z ident, right associativity) : type_scope.

Notation " 'exists' x y z w , p" := (ex (fun x => (ex (fun y => (ex (fun z => (ex (fun w => p))))))))
  (at level 200, x ident, y ident, z ident, w ident, right associativity) : type_scope.

Tactic Notation "exist" constr(x) := exists x.
Tactic Notation "exist" constr(x) constr(y) := exists x ; exists y.
Tactic Notation "exist" constr(x) constr(y) constr(z) := exists x ; exists y ; exists z.
Tactic Notation "exist" constr(x) constr(y) constr(z) constr(w) := exists x ; exists y ; exists z ; exists w.

(* Notation " 'Σ' x : T , p" := (sigT (fun x : T => p)) *)
(*   (at level 200, x ident, y ident, right associativity) : program_scope. *)

(* Notation " 'Π' x : T , p " := (forall x : T, p) *)
(*   (at level 200, x ident, right associativity) : program_scope. *)