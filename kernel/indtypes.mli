(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Declarations
open Environ
open Entries
open Typeops
(*i*)


(*s The different kinds of errors that may result of a malformed inductive
  definition. *)

type inductive_error =
  (* These are errors related to inductive constructions in this module *)
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry
  (* These are errors related to recursors building in Indrec *)
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme

exception InductiveError of inductive_error

(*s The following function does checks on inductive declarations. *)

val check_inductive :
  env -> mutual_inductive_entry -> mutual_inductive_body
