(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** This module defines quantification on the world [Type]
    ([Logic.v] was defining it on the world [Set]) *)

Require Export Logic.
Require LogicSyntax.


(** [allT A P], or simply [(ALLT x | P(x))], stands for [(x:A)(P x)]
   when [A] is of type [Type] *)

(*
Definition allT := [A:Type][P:A->Prop](x:A)(P x). 
*)

Syntactic Definition allT := all.

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

(** * Existential Quantification *)

(** [exT A P], or simply [(EXT x | P(x))], stands for the existential 
    quantification on the predicate [P] when [A] is of type [Type] *)

(** [exT2 A P Q], or simply [(EXT x | P(x) & Q(x))], stands for the
    existential quantification on both [P] and [Q] when [A] is of
    type [Type] *)
(*
Inductive  exT [A:Type;P:A->Prop] : Prop
    := exT_intro : (x:A)(P x)->(exT A P).
*)

Syntactic Definition exT := ex.
Syntactic Definition exT_intro := ex_intro.
Syntactic Definition exT_ind  := ex_ind.

(*
Inductive exT2 [A:Type;P,Q:A->Prop] : Prop
    := exT_intro2 : (x:A)(P x)->(Q x)->(exT2 A P Q).
*)

Syntactic Definition exT2 := ex2.
Syntactic Definition exT_intro2 := ex_intro2.
Syntactic Definition exT2_ind  := ex2_ind.

(** Leibniz equality : [A:Type][x,y:A] (P:A->Prop)(P x)->(P y)

   [eqT A x y], or simply [x==y], is Leibniz' equality when [A] is of 
   type [Type]. This equality satisfies reflexivity (by definition), 
   symmetry, transitivity and stability by congruence *)


(*
Inductive eqT [A:Type;x:A] : A -> Prop
                       := refl_eqT : (eqT A x x).

Hints Resolve refl_eqT (* exT_intro2 exT_intro *) : core v62.
*)
Syntactic Definition eqT      := eq.
Syntactic Definition refl_eqT := refl_equal.
Syntactic Definition eqT_ind  := eq_ind.
Syntactic Definition eqT_rect := eq_rect.
Syntactic Definition eqT_rec  := eq_rec.

(*
Section Equality_is_a_congruence.

 Variables A,B : Type.
 Variable  f : A->B.

 Variable x,y,z : A.
 
 Lemma sym_eqT : (eqT ? x y) -> (eqT ? y x).
 Proof.
  Induction 1; Trivial.
 Qed.

 Lemma trans_eqT : (eqT ? x y) -> (eqT ? y z) -> (eqT ? x z).
 Proof.
  Induction 2; Trivial.
 Qed.

 Lemma congr_eqT : (eqT ? x y)->(eqT ? (f x) (f y)).
 Proof.
  Induction 1; Trivial.
 Qed.

 Lemma sym_not_eqT : ~(eqT ? x y) -> ~(eqT ? y x).
 Proof.
  Red; Intros H H'; Apply H; Elim H'; Trivial.
 Qed.

End Equality_is_a_congruence.
*)
Syntactic Definition sym_eqT  := sym_eq.
Syntactic Definition trans_eqT  := trans_eq.
Syntactic Definition congr_eqT  := f_equal.
Syntactic Definition sym_not_eqT  := sym_not_eq.

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

Syntactic Definition eqT_ind_r  := eq_ind_r.
Syntactic Definition eqT_rec_r  := eq_rec_r.
Syntactic Definition eqT_rect_r  := eq_rect_r.

(** Some datatypes at the [Type] level *)

Inductive EmptyT: Type :=.
Inductive UnitT : Type := IT : UnitT.

Definition notT := [A:Type] A->EmptyT.

(** Have you an idea of what means [identityT A a b]? No matter! *)

Inductive identityT [A:Type; a:A] : A->Type :=
     refl_identityT : (identityT A a a).

Hints Resolve refl_identityT : core v62.

Section IdentityT_is_a_congruence.

 Variables A,B : Type.
 Variable  f : A->B.

 Variable x,y,z : A.
 
 Lemma sym_idT : (identityT ? x y) -> (identityT ? y x).
 Proof.
  Induction 1; Trivial.
 Qed.

 Lemma trans_idT : (identityT ? x y) -> (identityT ? y z) -> (identityT ? x z).
 Proof.
  Induction 2; Trivial.
 Qed.

 Lemma congr_idT : (identityT ? x y)->(identityT ? (f x) (f y)).
 Proof.
  Induction 1; Trivial.
 Qed.

 Lemma sym_not_idT : (notT (identityT ? x y)) -> (notT (identityT ? y x)).
 Proof.
  Red; Intros H H'; Apply H; Elim H'; Trivial.
 Qed.

End IdentityT_is_a_congruence.

Definition identityT_ind_r :
     (A:Type)
        (a:A)
         (P:A->Prop)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_idT with 1:= H0; Trivial.
Defined.

Definition identityT_rec_r :      
     (A:Type)
        (a:A)
         (P:A->Set)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_idT with 1:= H0; Trivial.
Defined.

Definition identityT_rect_r :      
     (A:Type)
        (a:A)
         (P:A->Type)
          (P a)->(y:A)(identityT ? y a)->(P y).
 Intros A x P H y H0; Case sym_idT with 1:= H0; Trivial.
Defined.

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

Hints Immediate sym_idT sym_not_idT : core v62.

Implicits fstT [1 2].
Implicits sndT [1 2].
Implicits pairT [1 2].
