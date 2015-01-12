(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Cic
open Environ
(*i*)

val prkn : kernel_name -> Pp.std_ppcmds
val prcon : constant -> Pp.std_ppcmds

(*s The different kinds of errors that may result of a malformed inductive
  definition. *)

(* Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of Id.t
  | BadEntry

exception InductiveError of inductive_error

(*s The following function does checks on inductive declarations. *)

val check_inductive : env -> mutual_inductive -> mutual_inductive_body -> env
