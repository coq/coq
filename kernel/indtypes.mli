(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Declarations
open Environ
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
  | NotAnArity of identifier
  | BadEntry
  (* These are errors related to recursors building in Indrec *)
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme

exception InductiveError of inductive_error

(*s The following function does checks on inductive declarations. *)

(* [mind_check_wellformed env mie] checks that the types declared for
   all the inductive types are arities. It checks also that
   constructor and inductive names altogether are distinct. It raises
   an exception [InductiveError _] if [mie] is not well-formed *)

val mind_check_wellformed : env -> mutual_inductive_entry -> unit

(* [cci_inductive] checks positivity and builds an inductive body *)

val cci_inductive : 
  (identifier * variable_path) list -> env -> env -> path_kind -> bool -> 
   (Sign.rel_context * int * identifier * types * 
    identifier list * bool * bool * types array)
      list ->
      constraints ->
      	mutual_inductive_body
