(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Various syntaxic shortands that are useful with [Program]. *)

Require Export Coq.Program.Tactics.

Set Implicit Arguments.

(** A simpler notation for subsets defined on a cartesian product. *)

Notation "{ ( x , y )  :  A  |  P }" :=
  (sig (fun anonymous : A => let (x,y) := anonymous in P))
  (x ident, y ident, at level 10) : type_scope.

(** Generates an obligation to prove False. *)

Notation " ! " := (False_rect _ _) : program_scope.

Delimit Scope program_scope with prg.

(** Abbreviation for first projection and hiding of proofs of subset objects. *)

Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : program_scope.

(** Coerces objects to their support before comparing them. *)

Notation " x '`=' y " := ((x :>) = (y :>)) (at level 70) : program_scope.

Require Import Coq.Bool.Sumbool.

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
