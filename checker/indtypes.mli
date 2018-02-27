(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Names
open Cic
open Environ
(*i*)

val prkn : KerName.t -> Pp.t
val prcon : Constant.t -> Pp.t

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

val check_inductive : env -> MutInd.t -> mutual_inductive_body -> env
