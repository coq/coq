(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Identifier
open Term
open Sign
open Environ
open Type_errors
open Indtypes
(*i*)

(* This module provides functions to explain the various typing errors.
   It is parameterized by a function to pretty-print a term in a given
   context. *)

module type Printer = sig
  val pr_term : env -> constr -> std_ppcmds
end

(*s The result is a module which provides a function [explain_type_error]
  to explain a type error for a given kind in a given env, which are 
  usually the three arguments carried by the exception [TypeError] 
  (see \refsec{typeerrors}). *)

module Make (P : Printer) : sig

val explain_type_error : env -> type_error -> std_ppcmds

val pr_ne_ctx : std_ppcmds -> env -> std_ppcmds

val explain_unbound_rel : env -> int -> std_ppcmds

val explain_not_type : env -> constr -> std_ppcmds

val explain_bad_assumption : env -> constr -> std_ppcmds
 
val explain_reference_variables : identifier -> std_ppcmds

val explain_elim_arity : 
  env -> constr -> constr list -> constr 
    -> unsafe_judgment -> (constr * constr * string) option -> std_ppcmds

val explain_case_not_inductive : 
  env -> unsafe_judgment -> std_ppcmds

val explain_number_branches : 
  env -> unsafe_judgment -> int -> std_ppcmds

val explain_ill_formed_branch :
  env -> constr -> int -> constr -> constr -> std_ppcmds

val explain_generalization :
  env -> name * types -> constr -> std_ppcmds

val explain_actual_type :
  env -> constr -> constr -> constr -> std_ppcmds

val explain_ill_formed_rec_body :
  env -> guard_error -> 
    name array -> int -> constr array -> std_ppcmds

val explain_ill_typed_rec_body  :
  env -> int -> name list -> unsafe_judgment array 
    -> types array -> std_ppcmds

val explain_inductive_error :  inductive_error -> std_ppcmds

end
