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

(** This module defines quantification on the world [Type]
    ([Logic.v] was defining it on the world [Set]) *)

Require Datatypes.
Require Export Logic.

V7only [
(*
(** [allT A P], or simply [(ALLT x | P(x))], stands for [(x:A)(P x)]
   when [A] is of type [Type] *)

Definition allT := [A:Type][P:A->Prop](x:A)(P x). 
*)

Notation allT := all (only parsing).
Notation inst := Logic.inst (only parsing).
Notation gen := Logic.gen (only parsing).

(* Order is important to give printing priority to fully typed ALL and EX *)

Notation AllT := (all ?).
Notation "'ALLT' x | p"     := (all ? [x]p)   (at level 10, p at level 8).
Notation "'ALLT' x : t | p" := (all ? [x:t]p) (at level 10, p at level 8).

(*
Section universal_quantification.

Variable A : Type.
Variable P : A->Prop.

Theorem inst :  (x:A)(allT ? [x](P x))->(P x).
Proof.
Unfold all; Auto.
Qed.

Theorem gen : (B:Prop)(f:(y:A)B->(P y))B->(allT A P).
Proof.
Red; Auto.
Qed.

End universal_quantification.
*)

(*
(** * Existential Quantification *)

(** [exT A P], or simply [(EXT x | P(x))], stands for the existential 
    quantification on the predicate [P] when [A] is of type [Type] *)

(** [exT2 A P Q], or simply [(EXT x | P(x) & Q(x))], stands for the
    existential quantification on both [P] and [Q] when [A] is of
    type [Type] *)
Inductive  exT [A:Type;P:A->Prop] : Prop
    := exT_intro : (x:A)(P x)->(exT A P).
*)

Notation exT := ex (only parsing).
Notation exT_intro := ex_intro (only parsing).
Notation exT_ind  := ex_ind (only parsing).

Notation ExT  := (ex ?).
Notation "'EXT' x | p"      := (ex ? [x]p)
  (at level 10, p at level 8, only parsing).
Notation "'EXT' x : t | p"  := (ex ? [x:t]p)
  (at level 10, p at level 8, only parsing).

(*
Inductive exT2 [A:Type;P,Q:A->Prop] : Prop
    := exT_intro2 : (x:A)(P x)->(Q x)->(exT2 A P Q).
*)

Notation exT2 := ex2 (only parsing).
Notation exT_intro2 := ex_intro2 (only parsing).
Notation exT2_ind  := ex2_ind (only parsing).

Notation ExT2 := (ex2 ?).
Notation "'EXT' x | p & q"     := (ex2 ? [x]p [x]q)
  (at level 10, p, q at level 8).
Notation "'EXT' x : t | p & q" := (ex2 ? [x:t]p [x:t]q)
  (at level 10, p, q at level 8).

(*
(** Leibniz equality : [A:Type][x,y:A] (P:A->Prop)(P x)->(P y)

   [eqT A x y], or simply [x==y], is Leibniz' equality when [A] is of 
   type [Type]. This equality satisfies reflexivity (by definition), 
   symmetry, transitivity and stability by congruence *)


Inductive eqT [A:Type;x:A] : A -> Prop
                       := refl_eqT : (eqT A x x).

Hints Resolve refl_eqT (* exT_intro2 exT_intro *) : core v62.
*)

Notation eqT      := eq (only parsing).
Notation refl_eqT := refl_equal (only parsing).
Notation eqT_ind  := eq_ind (only parsing).
Notation eqT_rect := eq_rect (only parsing).
Notation eqT_rec  := eq_rec (only parsing).

Notation "x == y"  := (eq ? x y) (at level 5, no associativity, only parsing).

(** Parsing only of things in [Logic_type.v] *)

Notation "< A > x == y"  := (eq A x y)
   (A annot, at level 1, x at level 0, only parsing).

(*
Section Equality_is_a_congruence.

 Variables A,B : Type.
 Variable  f : A->B.

 Variable x,y,z : A.
 
 Lemma sym_eqT : (eqT ? x y) -> (eqT ? y x).
 Proof.
  NewDestruct 1; Trivial.
 Qed.

 Lemma trans_eqT : (eqT ? x y) -> (eqT ? y z) -> (eqT ? x z).
 Proof.
  NewDestruct 2; Trivial.
 Qed.

 Lemma congr_eqT : (eqT ? x y)->(eqT ? (f x) (f y)).
 Proof.
  NewDestruct 1; Trivial.
 Qed.

 Lemma sym_not_eqT : ~(eqT ? x y) -> ~(eqT ? y x).
 Proof.
  Red; Intros H H'; Apply H; NewDestruct H'; Trivial.
 Qed.

End Equality_is_a_congruence.
*)

Notation sym_eqT  := sym_eq (only parsing).
Notation trans_eqT  := trans_eq (only parsing).
Notation congr_eqT  := f_equal (only parsing).
Notation sym_not_eqT  := sym_not_eq (only parsing).

(*
Hints Immediate sym_eqT sym_not_eqT : core v62.
*)

(** This states the replacement of equals by equals *)

(*
Definition eqT_ind_r : (A:Type)(x:A)(P:A->Prop)(P x)->(y:A)(eqT ? y x)->(P y).
Intros A x P H y H0; Case sym_eqT with 1:=H0; Trivial.
Defined.

Definition eqT_rec_r : (A:Type)(x:A)(P:A->Set)(P x)->(y:A)(eqT ? y x)->(P y).
Intros A x P H y H0; Case sym_eqT with 1:=H0; Trivial.
Defined.

Definition eqT_rect_r : (A:Type)(x:A)(P:A->Type)(P x)->(y:A)(eqT ? y x)->(P y).
Intros A x P H y H0; Case sym_eqT with 1:=H0; Trivial.
Defined.
*)

Notation eqT_ind_r  := eq_ind_r (only parsing).
Notation eqT_rec_r  := eq_rec_r (only parsing).
Notation eqT_rect_r  := eq_rect_r (only parsing).

(** Some datatypes at the [Type] level *)
(*
Inductive EmptyT: Type :=.
Inductive UnitT : Type := IT : UnitT.
*)

Notation EmptyT := False (only parsing).
Notation UnitT := unit (only parsing).
Notation IT := tt.
].
Definition notT := [A:Type] A->EmptyT.

V7only [
(** Have you an idea of what means [identityT A a b]? No matter! *)

(*
Inductive identityT [A:Type; a:A] : A -> Type :=
     refl_identityT : (identityT A a a).
*)

Notation identityT := identity (only parsing).
Notation refl_identityT := refl_identity (only parsing).

Notation "< A > x === y" := (!identityT A x y)
   (A annot, at level 1, x at level 0, only parsing) : type_scope.

Notation "x === y" := (identityT ? x y)
  (at level 5, no associativity, only parsing) : type_scope.

(*
Hints Resolve refl_identityT : core v62.
*)
].
Section identity_is_a_congruence.

 Variables A,B : Type.
 Variable  f : A->B.

 Variable x,y,z : A.
 
 Lemma sym_id : (identityT ? x y) -> (identityT ? y x).
 Proof.
  NewDestruct 1; Trivial.
 Qed.

 Lemma trans_id : (identityT ? x y) -> (identityT ? y z) -> (identityT ? x z).
 Proof.
  NewDestruct 2; Trivial.
 Qed.

 Lemma congr_id : (identityT ? x y)->(identityT ? (f x) (f y)).
 Proof.
  NewDestruct 1; Trivial.
 Qed.

 Lemma sym_not_id : (notT (identityT ? x y)) -> (notT (identityT ? y x)).
 Proof.
  Red; Intros H H'; Apply H; NewDestruct H'; Trivial.
 Qed.

End identity_is_a_congruence.

Definition identity_ind_r :
     (A:Type)
        (a:A)
         (P:A->Prop)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_id with 1:= H0; Trivial.
Defined.

Definition identity_rec_r :      
     (A:Type)
        (a:A)
         (P:A->Set)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_id with 1:= H0; Trivial.
Defined.

Definition identity_rect_r :      
     (A:Type)
        (a:A)
         (P:A->Type)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_id with 1:= H0; Trivial.
Defined.

V7only [
Notation sym_idT  := sym_id (only parsing).
Notation trans_idT  := trans_id (only parsing).
Notation congr_idT  := congr_id (only parsing).
Notation sym_not_idT  := sym_not_id (only parsing).
Notation identityT_ind_r := identity_ind_r (only parsing).
Notation identityT_rec_r  := identity_rec_r (only parsing).
Notation identityT_rect_r := identity_rect_r (only parsing).
].
Inductive prodT [A,B:Type] : Type := pairT : A -> B -> (prodT A B).

Section prodT_proj.

  Variables A, B : Type.

  Definition fstT := [H:(prodT A B)]Cases H of (pairT x _) => x end.
  Definition sndT := [H:(prodT A B)]Cases H of (pairT _ y) => y end.

End prodT_proj.

Definition prodT_uncurry : (A,B,C:Type)((prodT A B)->C)->A->B->C :=
  [A,B,C:Type; f:((prodT A B)->C); x:A; y:B]
  (f (pairT A B x y)).

Definition prodT_curry : (A,B,C:Type)(A->B->C)->(prodT A B)->C :=
  [A,B,C:Type; f:(A->B->C); p:(prodT A B)]
  Cases p of
  | (pairT x y) => (f x y)
  end.

Hints Immediate sym_id sym_not_id : core v62.

V7only [
Implicits fstT [1 2].
Implicits sndT [1 2].
Implicits pairT [1 2].
].
