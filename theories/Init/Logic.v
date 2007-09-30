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

(** [(IF_then_else P Q R)], written [IF P then Q else R] denotes
    either [P] and [Q], or [~P] and [Q] *)

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

(** Remark: [exists x, Q] denotes [ex (fun x => Q)] so that [exists x,
   P x] is in fact equivalent to [ex (fun x => P x)] which may be not
   convertible to [ex P] if [P] is not itself an abstraction *)


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
    format "'[' 'exists'  '/  ' x  :  t ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
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

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of 
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

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

(** Basic definitions about relations and properties *)

Definition subrelation (A B : Type) (R R' : A->B->Prop) :=
  forall x y, R x y -> R' x y.

Definition unique (A : Type) (P : A->Prop) (x:A) :=
  P x /\ forall (x':A), P x' -> x=x'.

Definition uniqueness (A:Type) (P:A->Prop) := forall x y, P x -> P y -> x = y.

(** Unique existence *)

Notation "'exists' ! x , P" := (ex (unique (fun x => P)))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x ,  '/  ' P ']'") : type_scope.
Notation "'exists' ! x : A , P" := 
  (ex (unique (fun x:A => P)))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' !  '/  ' x  :  A ,  '/  ' P ']'") : type_scope.

Lemma unique_existence : forall (A:Type) (P:A->Prop),
  ((exists x, P x) /\ uniqueness P) <-> (exists! x, P x).
Proof.
  intros A P; split.
  intros ((x,Hx),Huni); exists x; red; auto.
  intros (x,(Hx,Huni)); split. 
  exists x; assumption.
  intros x' x'' Hx' Hx''; transitivity x.
  symmetry; auto.
  auto.
Qed.

(** Being inhabited *)

Inductive inhabited (A:Type) : Prop := inhabits : A -> inhabited A.

Hint Resolve inhabits: core.
