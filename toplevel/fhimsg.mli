(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
open Type_errors
(*i*)

(* This module provides functions to explain the various typing errors.
   It is parameterized by a function to pretty-print a term in a given
   context. *)

module type Printer = sig
  val pr_term : path_kind -> env -> constr -> std_ppcmds
end

(*s The result is a module which provides a function [explain_type_error]
  to explain a type error for a given kind in a given env, which are 
  usually the three arguments carried by the exception [TypeError] 
  (see \refsec{typeerrors}). *)

module Make (P : Printer) : sig

val explain_type_error : path_kind -> env -> type_error -> std_ppcmds

val pr_ne_ctx : std_ppcmds -> path_kind -> env -> std_ppcmds

val explain_unbound_rel : path_kind -> env -> int -> std_ppcmds

val explain_not_type : path_kind -> env -> constr -> std_ppcmds

val explain_bad_assumption : path_kind -> env -> constr -> std_ppcmds
 
val explain_reference_variables : identifier -> std_ppcmds

val explain_elim_arity : 
  path_kind -> env -> constr -> constr list -> constr 
    -> unsafe_judgment -> (constr * constr * string) option -> std_ppcmds

val explain_case_not_inductive : 
  path_kind -> env -> unsafe_judgment -> std_ppcmds

val explain_number_branches : 
  path_kind -> env -> unsafe_judgment -> int -> std_ppcmds

val explain_ill_formed_branch :
  path_kind -> env -> constr -> int -> constr -> constr -> std_ppcmds

val explain_generalization :
  path_kind -> env -> name * types -> constr -> std_ppcmds

val explain_actual_type :
  path_kind -> env -> constr -> constr -> constr -> std_ppcmds

val explain_ill_formed_rec_body :
  path_kind -> env -> guard_error -> 
    name array -> int -> constr array -> std_ppcmds

val explain_ill_typed_rec_body  :
  path_kind -> env -> int -> name list -> unsafe_judgment array 
    -> types array -> std_ppcmds

end
