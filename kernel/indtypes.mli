(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Univ
open Term
open Declarations
open Environ
open Entries
open Typeops


(** {6 Sect } *)
(** The different kinds of errors that may result of a malformed inductive
  definition. *)

(** Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * identifier * constr * constr * int * int
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry
  | LargeNonPropInductiveNotInType

exception InductiveError of inductive_error

(** {6 The following function does checks on inductive declarations. } *)

val check_inductive :
  env -> mutual_inductive_entry -> mutual_inductive_body
