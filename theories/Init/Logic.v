
(* $Id$ *)

Require Export Datatypes.

(* [True] is the always true proposition *)
Inductive True : Prop := I : True. 

(* [False] is the always false proposition *)
Inductive False : Prop := . 

(* [not A], written [~A], is the negation of [A] *)
Definition not := [A:Prop]A->False.

Hints Unfold not : core.

Section Conjunction.

  (* [and A B], written [A /\ B], is the conjunction of [A] and [B] *)
  (* [conj A B p q], written [<p,q>] is a proof of [A /\ B] as soon as 
     [p] is a proof of [A] and [q] a proof of [B] *)
  (* [proj1] and [proj2] are first and second projections of a conjunction *)

  Inductive and [A,B:Prop] : Prop := conj : A -> B -> (and A B).

  Variables A,B : Prop.

  Theorem proj1 : (and A B) -> A.
  Proof.
  Induction 1; Trivial.
  Qed.

  Theorem proj2 : (and A B) -> B.
  Proof.
  Induction 1; Trivial.
  Qed.

End Conjunction.

Section Disjunction.

  (* [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

  Inductive or [A,B:Prop] : Prop :=
       or_introl : A -> (or A B) 
     | or_intror : B -> (or A B).

End Disjunction.

Section Equivalence.

  (* [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

  Definition iff := [P,Q:Prop] (and (P->Q) (Q->P)).

End Equivalence.

(* [(IF P Q R)], or more suggestively [(either P and_then Q or_else R)],
   denotes either [P] and [Q], or [~P] and [Q] *)
Definition IF := [P,Q,R:Prop] (or (and P Q) (and (not P) R)).

Section First_order_quantifiers.

  (* [(ex A P)], or simply [(EX x | P(x))], expresses the existence of an 
     [x] of type [A] which satisfies the predicate [P] ([A] is of type 
     [Set]). This is existential quantification. *)

  (* [(ex2 A P Q)], or simply [(EX x | P(x) & Q(x))], expresses the
     existence of an [x] of type [A] which satisfies both the predicates
     [P] and [Q] *)

  (* Universal quantification (especially first-order one) is normally 
     written [(x:A)(P x)]. For duality with existential quantification, the 
     construction [(all A P)], or simply [(All P)], is provided as an 
     abbreviation of [(x:A)(P x)] *) 

  Inductive ex [A:Set;P:A->Prop] : Prop 
      := ex_intro : (x:A)(P x)->(ex A P).

  Inductive ex2 [A:Set;P,Q:A->Prop] : Prop
      := ex_intro2 : (x:A)(P x)->(Q x)->(ex2 A P Q).

  Definition all := [A:Set][P:A->Prop](x:A)(P x). 

End First_order_quantifiers.

Section Equality.

  (* [(eq A x y)], or simply [x=y], expresses the (Leibniz') equality
     of [x] and [y]. Both [x] and [y] must belong to the same type [A].
     The definition is inductive and states the reflexivity of the equality.
     The others properties (symmetry, transitivity, replacement of 
     equals) are proved below *)

  Inductive eq [A:Set;x:A] : A->Prop
         := refl_equal : (eq A x x).

End Equality.

Hints Resolve I conj or_introl or_intror refl_equal : core v62.
Hints Resolve ex_intro ex_intro2 : core v62.

Section Logic_lemmas.

  Theorem absurd : (A:Prop)(C:Prop) A -> (not A) -> C.
  Proof.
    Unfold not; Intros A C h1 h2.
    Elim (h2 h1).
  Qed.

  Section equality.
    Variable A,B : Set.
    Variable f   : A->B.
    Variable x,y,z : A.

    Theorem sym_eq : (eq ? x y) -> (eq ? y x).
      Proof.
     Induction 1; Trivial.
    Qed.

    Theorem trans_eq : (eq ? x y) -> (eq ? y z) -> (eq ? x z).
    Proof.
     Induction 2; Trivial.
    Qed.

    Theorem f_equal : (eq ? x y) -> (eq ? (f x) (f y)).
    Proof.
     Induction 1; Trivial.
    Qed.

    Theorem sym_not_eq : (not (eq ? x y)) -> (not (eq ? y x)).
    Proof.
     Red; Intros h1 h2; Apply h1; Elim h2; Trivial.
    Qed.

    Definition sym_equal     := sym_eq.
    Definition sym_not_equal := sym_not_eq.
    Definition trans_equal   := trans_eq.

  End equality.

  Theorem eq_rect: (A:Set)(x:A)(P:A->Type)(P x)->(y:A)(eq ? x y)->(P y).
  Proof.
   Intros.
   Cut (identity A x y).
   Destruct 1; Auto.
   Elim H; Auto.
  Qed.

  Definition eq_ind_r : (A:Set)(x:A)(P:A->Prop)(P x)->(y:A)(eq ? y x)->(P y).
   Intros A x P H y H0; Case sym_eq with 1:= H0; Trivial.
  Defined.

  Definition eq_rec_r : (A:Set)(x:A)(P:A->Set)(P x)->(y:A)(eq ? y x)->(P y).
    Intros A x P H y H0; Case sym_eq with 1:= H0; Trivial.
  Defined.

  Definition eq_rect_r : (A:Set)(x:A)(P:A->Type)(P x)->(y:A)(eq ? y x)->(P y).
    Intros A x P H y H0; Elim sym_eq with 1:= H0; Trivial.
  Defined.
End Logic_lemmas.

Theorem f_equal2 : (A1,A2,B:Set)(f:A1->A2->B)(x1,y1:A1)(x2,y2:A2)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? (f x1 x2) (f y1 y2)).
Proof.
  Induction 1; Induction 1; Trivial.
Qed.

Theorem f_equal3 : (A1,A2,A3,B:Set)(f:A1->A2->A3->B)(x1,y1:A1)(x2,y2:A2)
  (x3,y3:A3)(eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) 
   -> (eq ? (f x1 x2 x3) (f y1 y2 y3)).
Proof.
  Induction 1; Induction 1; Induction 1; Trivial.
Qed.

Theorem f_equal4 : (A1,A2,A3,A4,B:Set)(f:A1->A2->A3->A4->B)
  (x1,y1:A1)(x2,y2:A2)(x3,y3:A3)(x4,y4:A4)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) -> (eq ? x4 y4)
   -> (eq ? (f x1 x2 x3 x4) (f y1 y2 y3 y4)).
Proof.
  Induction 1; Induction 1; Induction 1; Induction 1; Trivial.
Qed.

Theorem f_equal5 : (A1,A2,A3,A4,A5,B:Set)(f:A1->A2->A3->A4->A5->B)
  (x1,y1:A1)(x2,y2:A2)(x3,y3:A3)(x4,y4:A4)(x5,y5:A5)
  (eq ? x1 y1) -> (eq ? x2 y2) -> (eq ? x3 y3) -> (eq ? x4 y4) -> (eq ? x5 y5)
    -> (eq ? (f x1 x2 x3 x4 x5) (f y1 y2 y3 y4 y5)).
Proof.
  Induction 1; Induction 1; Induction 1; Induction 1; Induction 1; Trivial.
Qed.

Hints Immediate sym_eq sym_not_eq : core v62.

Syntactic Definition Ex := ex | 1.
Syntactic Definition Ex2 := ex2 | 1.
Syntactic Definition All := all | 1.
