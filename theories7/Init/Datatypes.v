(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Notations.
Require Logic.

Set Implicit Arguments.
V7only [Unset Implicit Arguments.].

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set := tt : unit.

(** [bool] is the datatype of the booleans values [true] and [false] *)

Inductive bool : Set := true : bool 
                      | false : bool.

Add Printing If bool.

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that zero is the letter O, not the numeral 0 *)

Inductive nat : Set := O : nat 
                     | S : nat->nat.

Delimits Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments Scope S [ nat_scope ].

(** [Empty_set] has no inhabitant *)

Inductive Empty_set:Set :=.

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity [A:Type; a:A] : A->Set :=
     refl_identity: (identity A a a).
Hints Resolve refl_identity : core v62.

Implicits identity_ind [1].
Implicits identity_rec [1].
Implicits identity_rect [1].
V7only [
Implicits identity_ind [].
Implicits identity_rec [].
Implicits identity_rect [].
].

(** [option A] is the extension of A with a dummy element None *)

Inductive option [A:Set] : Set := Some : A -> (option A) | None : (option A).

Implicits None [1].
V7only [Implicits None [].].

(** [sum A B], equivalently [A + B], is the disjoint sum of [A] and [B] *)
(* Syntax defined in Specif.v *)
Inductive sum [A,B:Set] : Set
    := inl : A -> (sum A B)
     | inr : B -> (sum A B).

Notation "x + y" := (sum x y) : type_scope.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod [A,B:Set] : Set := pair : A -> B -> (prod A B).
Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
V7only [Notation "( x , y )" := (pair ? ? x y) : core_scope.].
V8Notation "( x , y , .. , z )" := (pair ? ? .. (pair ? ? x y) .. z) : core_scope.

Section projections.
   Variables A,B:Set.
   Definition fst := [p:(prod A B)]Cases p of (pair x y) => x end.
   Definition snd := [p:(prod A B)]Cases p of (pair x y) => y end.
End projections. 

V7only [
Notation Fst := (fst ? ?).
Notation Snd := (snd ? ?).
].
Hints Resolve pair inl inr : core v62.

Lemma surjective_pairing : (A,B:Set;p:A*B)p=(pair A B (Fst p) (Snd p)).
Proof.
NewDestruct p; Reflexivity.
Qed.

Lemma injective_projections : 
 (A,B:Set;p1,p2:A*B)(Fst p1)=(Fst p2)->(Snd p1)=(Snd p2)->p1=p2.
Proof.
NewDestruct p1; NewDestruct p2; Simpl; Intros Hfst Hsnd.
Rewrite Hfst; Rewrite Hsnd; Reflexivity. 
Qed.

V7only[
(** Parsing only of things in [Datatypes.v] *)
Notation "< A , B > ( x , y )" := (pair A B x y) (at level 1, only parsing, A annot).
Notation "< A , B > 'Fst' ( p )" := (fst A B p) (at level 1, only parsing, A annot).
Notation "< A , B > 'Snd' ( p )" := (snd A B p) (at level 1, only parsing, A annot).
].

(** Comparison *)

Inductive relation : Set := 
  EGAL :relation | INFERIEUR : relation | SUPERIEUR : relation.

Definition Op := [r:relation]
  Cases r of
    EGAL => EGAL
  | INFERIEUR => SUPERIEUR
  | SUPERIEUR => INFERIEUR
  end.
