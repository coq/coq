
(* $Id$ *)

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
  val pr_term : path_kind -> context -> constr -> std_ppcmds
end

(*s The result is a module which provides a function [explain_type_error]
  to explain a type error for a given kind in a given context, which are 
  usually the three arguments carried by the exception [TypeError] 
  (see \refsec{typeerrors}). *)

module Make (P : Printer) : sig

val explain_type_error : path_kind -> context -> type_error -> std_ppcmds

val pr_ne_ctx : std_ppcmds -> path_kind -> context -> std_ppcmds

val explain_unbound_rel : path_kind -> context -> int -> std_ppcmds

val explain_cant_execute : path_kind -> context -> constr -> std_ppcmds

val explain_not_type : path_kind -> context -> constr -> std_ppcmds

val explain_bad_assumption : path_kind -> context -> constr -> std_ppcmds
 
val explain_reference_variables : identifier -> std_ppcmds

val explain_elim_arity : 
  path_kind -> context -> constr -> constr list -> constr 
    -> constr -> constr -> (constr * constr * string) option -> std_ppcmds

val explain_case_not_inductive : 
  path_kind -> context -> constr -> constr -> std_ppcmds

val explain_number_branches : 
  path_kind -> context -> constr -> constr -> int -> std_ppcmds

val explain_ill_formed_branch :
  path_kind -> context -> constr -> int -> constr -> constr -> std_ppcmds

val explain_generalization :
  path_kind -> context -> name * typed_type -> constr -> std_ppcmds

val explain_actual_type :
  path_kind -> context -> constr -> constr -> constr -> std_ppcmds

val explain_cant_apply : 
  path_kind -> context -> string -> unsafe_judgment 
    -> unsafe_judgment list -> std_ppcmds

val explain_ill_formed_rec_body :
  path_kind -> context -> std_ppcmds -> 
    name list -> int -> constr array -> std_ppcmds

val explain_ill_typed_rec_body  :
  path_kind -> context -> int -> name list -> unsafe_judgment array 
    -> typed_type array -> std_ppcmds

end
