(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.
V7only [Unset Implicit Arguments.].

Require Notations.

(** [True] is the always true proposition *)
Inductive True : Prop := I : True. 

(** [False] is the always false proposition *)
Inductive False : Prop := . 

(** [not A], written [~A], is the negation of [A] *)
Definition not := [A:Prop]A->False.

Notation "~ x" := (not x) : type_scope.

Hints Unfold not : core.

Inductive and [A,B:Prop] : Prop := conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

V7only[
Notation "< P , Q > { p , q }" := (conj P Q p q) (P annot, at level 1).
].

Section Conjunction.

  (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj A B p q], written [<p,q>] is a proof of [A /\ B] as soon as 
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

  Variables A,B : Prop.

  Theorem proj1 : (and A B) -> A.
  Proof.
  NewDestruct 1; Trivial.
  Qed.

  Theorem proj2 : (and A B) -> B.
  Proof.
  NewDestruct 1; Trivial.
  Qed.

End Conjunction.

(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Inductive or [A,B:Prop] : Prop :=
     or_introl : A -> A \/ B 
   | or_intror : B -> A \/ B

where "A \/ B" := (or A B) : type_scope.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff := [A,B:Prop] (and (A->B) (B->A)).

Notation "A <-> B" := (iff A B) : type_scope.

Section Equivalence.

Theorem iff_refl : (A:Prop) (iff A A).
  Proof.
    Split; Auto.
  Qed.

Theorem iff_trans : (a,b,c:Prop) (iff a b) -> (iff b c) -> (iff a c).
  Proof.
    Intros A B C (H1,H2) (H3,H4); Split; Auto.
  Qed.

Theorem iff_sym : (A,B:Prop) (iff A B) -> (iff B A).
  Proof.
    Intros A B (H1,H2); Split; Auto.
  Qed.

End Equivalence.

(** [(IF P Q R)], or more suggestively [(either P and_then Q or_else R)],
    denotes either [P] and [Q], or [~P] and [Q] *)
Definition IF_then_else := [P,Q,R:Prop] (or (and P Q) (and (not P) R)).
V7only [Notation IF:=IF_then_else.].

Notation "'IF' c1 'then' c2 'else' c3" := (IF c1 c2 c3)
  (at level 1, c1, c2, c3 at level 8) : type_scope
  V8only (at level 200).

(** First-order quantifiers *)

  (** [ex A P], or simply [exists x, P x], expresses the existence of an 
      [x] of type [A] which satisfies the predicate [P] ([A] is of type 
      [Set]). This is existential quantification. *)

  (** [ex2 A P Q], or simply [exists2 x, P x & Q x], expresses the
      existence of an [x] of type [A] which satisfies both the predicates
      [P] and [Q] *)

  (** Universal quantification (especially first-order one) is normally 
      written [forall x:A, P x]. For duality with existential quantification, 
      the construction [all P] is provided too *)

Inductive ex [A:Type;P:A->Prop] : Prop 
    := ex_intro : (x:A)(P x)->(ex A P).

Inductive ex2 [A:Type;P,Q:A->Prop] : Prop
    := ex_intro2 : (x:A)(P x)->(Q x)->(ex2 A P Q).

Definition all := [A:Type][P:A->Prop](x:A)(P x). 

(* Rule order is important to give printing priority to fully typed exists *)

V7only [ Notation Ex  := (ex ?). ].
Notation "'EX' x | p"      := (ex ? [x]p)
  (at level 10, p at level 8) : type_scope
  V8only "'exists' x , p" (at level 200, x ident, p at level 99).
Notation "'EX' x : t | p"  := (ex ? [x:t]p)
  (at level 10, p at level 8) : type_scope
  V8only "'exists' x : t , p" (at level 200, x ident, p at level 99, format
  "'exists'  '/  ' x  :  t ,  '/  ' p").

V7only [ Notation Ex2 := (ex2 ?). ].
Notation "'EX' x | p & q"       := (ex2 ? [x]p [x]q)
  (at level 10, p, q at level 8) : type_scope
  V8only "'exists2' x , p & q" (at level 200, x ident, p, q at level 99).
Notation "'EX' x : t | p & q"   := (ex2 ? [x:t]p [x:t]q)
  (at level 10, p, q at level 8) : type_scope
  V8only "'exists2' x : t , p & q"
    (at level 200, x ident, t at level 200, p, q at level 99, format
    "'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']'").

V7only [Notation All := (all ?).
Notation "'ALL' x | p"     := (all ? [x]p)
  (at level 10, p at level 8) : type_scope
  V8only (at level 200, x ident, p at level 200).
Notation "'ALL' x : t | p" := (all ? [x:t]p)
  (at level 10, p at level 8) : type_scope
  V8only (at level 200, x ident, t, p at level 200).
].

(** Universal quantification *)

Section universal_quantification.

  Variable A : Type.
  Variable P : A->Prop.

  Theorem inst : (x:A)(all ? [x](P x))->(P x).
  Proof.
  Unfold all; Auto.
  Qed.

  Theorem gen : (B:Prop)(f:(y:A)B->(P y))B->(all A P).
  Proof.
  Red; Auto.
  Qed.

  End universal_quantification.

(** Equality *)

(** [eq A x y], or simply [x=y], expresses the (Leibniz') equality
    of [x] and [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of 
    equals) are proved below *)

Inductive eq [A:Type;x:A] : A->Prop
       := refl_equal : x = x :> A

where "x = y :> A" := (!eq A x y) : type_scope.

Notation "x = y" := (eq ? x y) : type_scope.
Notation "x <> y  :> T" := ~ (!eq T x y) : type_scope.
Notation "x <> y" := ~ x=y : type_scope.

Implicits eq_ind [1].
Implicits eq_rec [1].
Implicits eq_rect [1].
V7only [
Implicits eq_ind [].
Implicits eq_rec [].
Implicits eq_rect [].
].

Hints Resolve I conj or_introl or_intror refl_equal : core v62.
Hints Resolve ex_intro ex_intro2 : core v62.

Section Logic_lemmas.

  Theorem absurd : (A:Prop)(C:Prop) A -> (not A) -> C.
  Proof.
    Unfold not; Intros A C h1 h2.
    NewDestruct (h2 h1).
  Qed.

  Section equality.
    Variable A,B : Type.
    Variable f   : A->B.
    Variable x,y,z : A.

    Theorem sym_eq : (eq ? x y) -> (eq ? y x).
    Proof.
     NewDestruct 1; Trivial.
    Defined.
    Opaque sym_eq.

    Theorem trans_eq : (eq ? x y) -> (eq ? y z) -> (eq ? x z).
    Proof.
     NewDestruct 2; Trivial.
    Defined.
    Opaque trans_eq.

    Theorem f_equal : (eq ? x y) -> (eq ? (f x) (f y)).
    Proof.
     NewDestruct 1; Trivial.
    Defined.
    Opaque f_equal.

    Theorem sym_not_eq : (not (eq ? x y)) -> (not (eq ? y x)).
    Proof.
     Red; Intros h1 h2; Apply h1; NewDestruct h2; Trivial.
    Qed.

    Definition sym_equal     := sym_eq.
    Definition sym_not_equal := sym_not_eq.
    Definition trans_equal   := trans_eq.

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

  Definition eq_ind_r : (A:Type)(x:A)(P:A->Prop)(P x)->(y:A)(eq ? y x)->(P y).
   Intros A x P H y H0; Elim sym_eq with 1:= H0; Assumption.
  Defined.

  Definition eq_rec_r : (A:Type)(x:A)(P:A->Set)(P x)->(y:A)(eq ? y x)->(P y).
    Intros A x P H y H0; Elim sym_eq with 1:= H0; Assumption.
  Defined.

  Definition eq_rect_r : (A:Type)(x:A)(P:A->Type)(P x)->(y:A)(eq ? y x)->(P y).
    Intros A x P H y H0; Elim sym_eq with 1:= H0; Assumption.
  Defined.
End Logic_lemmas.

Theorem f_equal2 : (A1,A2,B:Type)(f:A1->A2->B)(x1,y1:A1)(x2,y2:A2)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? (f x1 x2) (f y1 y2)).
Proof.
  NewDestruct 1; NewDestruct 1; Reflexivity.
Qed.

Theorem f_equal3 : (A1,A2,A3,B:Type)(f:A1->A2->A3->B)(x1,y1:A1)(x2,y2:A2)
  (x3,y3:A3)(eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) 
   -> (eq ? (f x1 x2 x3) (f y1 y2 y3)).
Proof.
  NewDestruct 1; NewDestruct 1; NewDestruct 1; Reflexivity.
Qed.

Theorem f_equal4 : (A1,A2,A3,A4,B:Type)(f:A1->A2->A3->A4->B)
  (x1,y1:A1)(x2,y2:A2)(x3,y3:A3)(x4,y4:A4)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) -> (eq ? x4 y4)
   -> (eq ? (f x1 x2 x3 x4) (f y1 y2 y3 y4)).
Proof.
  NewDestruct 1; NewDestruct 1; NewDestruct 1; NewDestruct 1; Reflexivity.
Qed.

Theorem f_equal5 : (A1,A2,A3,A4,A5,B:Type)(f:A1->A2->A3->A4->A5->B)
  (x1,y1:A1)(x2,y2:A2)(x3,y3:A3)(x4,y4:A4)(x5,y5:A5)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) -> (eq ? x4 y4) -> (eq ? x5 y5)
    -> (eq ? (f x1 x2 x3 x4 x5) (f y1 y2 y3 y4 y5)).
Proof.
  NewDestruct 1; NewDestruct 1; NewDestruct 1; NewDestruct 1; NewDestruct 1;
  Reflexivity.
Qed.

Hints Immediate sym_eq sym_not_eq : core v62.

V7only[
(** Parsing only of things in [Logic.v] *)
Notation "< A > 'All' ( P )" :=(all A P) (A annot, at level 1, only parsing).
Notation "< A > x = y" := (eq A x y)
 (A annot, at level 1, x at level 0, only parsing).
Notation "< A > x <> y" := ~(eq A x y)
  (A annot, at level 1, x at level 0, only parsing).
].
