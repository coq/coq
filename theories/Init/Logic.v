(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

Require Import Notations.

(** * Propositional connectives *)

(** [True] is the always true proposition *)
Inductive True : Prop :=
    I : True. 

(** [False] is the always false proposition *)
Inductive False : Prop :=. 

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

Inductive and (A B:Prop) : Prop :=
    conj : A -> B -> A /\ B 
 where "A /\ B" := (and A B) : type_scope.


Section Conjunction.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as 
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

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

(** [(IF_then_else P Q R)], written [IF P then Q else R] denotes
    either [P] and [Q], or [~P] and [Q] *)

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.

(** * First-order quantifiers
  - [ex A P], or simply [exists x, P x], expresses the existence of an 
      [x] of type [A] which satisfies the predicate [P] ([A] is of type 
      [Set]). This is existential quantification.
  - [ex2 A P Q], or simply [exists2 x, P x & Q x], expresses the
      existence of an [x] of type [A] which satisfies both the predicates
      [P] and [Q].
  - Universal quantification (especially first-order one) is normally 
    written [forall x:A, P x]. For duality with existential quantification, 
    the construction [all P] is provided too.
*)

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
    ex_intro : forall x:A, P x -> ex (A:=A) P.

Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
    ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.

Definition all (A:Type) (P:A -> Prop) := forall x:A, P x. 

(* Rule order is important to give printing priority to fully typed exists *)

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : t , p" := (ex (fun x:t => p))
  (at level 200, x ident, right associativity, 
   format "'exists'  '/  ' x  :  t ,  '/  ' p")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
   format "'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']'")
  : type_scope.


(** Derived rules for universal quantification *)

Section universal_quantification.

  Variable A : Type.
  Variable P : A -> Prop.

  Theorem inst : forall x:A, all (fun x => P x) -> P x.
  Proof.
  unfold all in |- *; auto.
  Qed.

  Theorem gen : forall (B:Prop) (f:forall y:A, B -> P y), B -> all P.
  Proof.
  red in |- *; auto.
  Qed.

End universal_quantification.

(** * Equality *)

(** [eq x y], or simply [x=y], expresses the (Leibniz') equality
    of [x] and [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of 
    equals) are proved below. The type of [x] and [y] can be made explicit
    using the notation [x = y :> A] *)

Inductive eq (A:Type) (x:A) : A -> Prop :=
    refl_equal : x = x :>A 
 where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Implicit Arguments eq_ind [A].
Implicit Arguments eq_rec [A].
Implicit Arguments eq_rect [A].

Hint Resolve I conj or_introl or_intror refl_equal: core v62.
Hint Resolve ex_intro ex_intro2: core v62.

Section Logic_lemmas.

  Theorem absurd : forall A C:Prop, A -> ~ A -> C.
  Proof.
    unfold not in |- *; intros A C h1 h2.
    destruct (h2 h1).
  Qed.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem sym_eq : x = y -> y = x.
    Proof.
     destruct 1; trivial.
    Defined.
    Opaque sym_eq.

    Theorem trans_eq : x = y -> y = z -> x = z.
    Proof.
     destruct 2; trivial.
    Defined.
    Opaque trans_eq.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
     destruct 1; trivial.
    Defined.
    Opaque f_equal.

    Theorem sym_not_eq : x <> y -> y <> x.
    Proof.
     red in |- *; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

    Definition sym_equal := sym_eq.
    Definition sym_not_equal := sym_not_eq.
    Definition trans_equal := trans_eq.

  End equality.

(* Is now a primitive principle 
  Theorem eq_rect: (A:Type)(x:A)(P:A->Type)(P x)->(y:A)(eq ? x y)->(P y).
  Proof.
   Intros.
   Cut (identity A x y).
   NewDestruct 1; Auto.
   NewDestruct H; Auto.
  Qed.
*)

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
   intros A x P H y H0; elim sym_eq with (1 := H0); assumption.
  Defined.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim sym_eq with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim sym_eq with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

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

Hint Immediate sym_eq sym_not_eq: core v62.
