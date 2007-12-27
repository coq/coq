(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Coq.Program.Tactics.

Set Implicit Arguments.

(** Wrap a proposition inside a subset. *)

Notation " {{ x }} " := (tt : { y : unit | x }).

(** A simpler notation for subsets defined on a cartesian product. *)

(* Notation "{ ( x , y )  :  A  |  P }" :=  *)
(*   (sig (fun anonymous : A => let (x,y) := anonymous in P)) *)
(*   (x ident, y ident, at level 10) : type_scope. *)

(** Generates an obligation to prove False. *)

Notation " ! " := (False_rect _ _).

(** Abbreviation for first projection and hiding of proofs of subset objects. *)

(** The scope in which programs are typed (not their types). *)

Delimit Scope program_scope with prg.

Notation " ` t " := (proj1_sig t) (at level 10) : core_scope.

Delimit Scope subset_scope with subset.

(* In [subset_scope] to allow masking by redefinitions for particular types. *)
Notation "( x & ? )" := (@exist _ _ x _) : subset_scope.

(** Coerces objects to their support before comparing them. *)

Notation " x '`=' y " := ((x :>) = (y :>)) (at level 70).

(** Quantifying over subsets. *)

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Require Import Coq.Bool.Sumbool.

(** Construct a dependent disjunction from a boolean. *)

Notation "'dec'" := (sumbool_of_bool) (at level 0). 

(** The notations [in_right] and [in_left] construct objects of a dependent disjunction. *)

Notation in_right := (@right _ _ _).
Notation in_left := (@left _ _ _).

(** Extraction directives *)

Extraction Inline proj1_sig.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
(* Extract Inductive prod "'a" "'b" => " 'a * 'b " [ "(,)" ]. *)
(* Extract Inductive sigT => "prod" [ "" ]. *)
