(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Various syntactic shorthands that are useful with [Program]. *)

Require Export Stdlib.Program.Tactics.

Set Implicit Arguments.

(** A simpler notation for subsets defined on a cartesian product. *)

Notation "{ ( x , y )  :  A  |  P }" :=
  (sig (fun anonymous : A => let (x,y) := anonymous in P))
  (x name, y name) : type_scope.

Declare Scope program_scope.
Delimit Scope program_scope with prg.

(** Generates an obligation to prove False. *)

Notation " ! " := (False_rect _ _) : program_scope.

(** Abbreviation for first projection and hiding of proofs of subset objects. *)

Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : program_scope.

(** Coerces objects to their support before comparing them. *)

(** Construct a dependent disjunction from a boolean. *)

Notation dec := sumbool_of_bool.

(** The notations [in_right] and [in_left] construct objects of a dependent disjunction. *)

(** Hide proofs and generates obligations when put in a term. *)

Notation in_left := (@left _ _ _).
Notation in_right := (@right _ _ _).

(** Extraction directives *)
(*
Extraction Inline proj1_sig.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
(* Extract Inductive prod "'a" "'b" => " 'a * 'b " [ "(,)" ]. *)
(* Extract Inductive sigT => "prod" [ "" ]. *)
*)
