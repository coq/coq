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
open Util
open Names
open Term
open Sign
open Environ
open Rawterm
open Inductiveops
(*i*)

(*s The type of errors raised by the pretyper *)

type pretype_error =
  (* Old Case *)
  | CantFindCaseType of constr
  (* Unification *)
  | OccurCheck of existential_key * constr
  | NotClean of existential_key * constr * hole_kind
  | UnsolvableImplicit of hole_kind
  (* Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

(* Presenting terms without solved evars *)
val nf_evar :  Evd.evar_map -> constr -> constr
val j_nf_evar :  Evd.evar_map -> unsafe_judgment -> unsafe_judgment
val jl_nf_evar :
   Evd.evar_map -> unsafe_judgment list -> unsafe_judgment list
val jv_nf_evar :
   Evd.evar_map -> unsafe_judgment array -> unsafe_judgment array
val tj_nf_evar :
   Evd.evar_map -> unsafe_type_judgment -> unsafe_type_judgment


(* Raising errors *)
val error_actual_type_loc :
  loc -> env ->  Evd.evar_map -> unsafe_judgment -> constr -> 'b

val error_cant_apply_not_functional_loc : 
  loc -> env ->  Evd.evar_map ->
      unsafe_judgment -> unsafe_judgment list -> 'b

val error_cant_apply_bad_type_loc : 
  loc -> env ->  Evd.evar_map -> int * constr * constr -> 
      unsafe_judgment -> unsafe_judgment list -> 'b

val error_case_not_inductive_loc :
  loc -> env ->  Evd.evar_map -> unsafe_judgment -> 'b

val error_ill_formed_branch_loc : 
  loc -> env ->  Evd.evar_map ->
      constr -> int -> constr -> constr -> 'b

val error_number_branches_loc : 
  loc -> env ->  Evd.evar_map ->
      unsafe_judgment -> int -> 'b

val error_ill_typed_rec_body_loc :
  loc -> env ->  Evd.evar_map ->
      int -> name array -> unsafe_judgment array -> types array -> 'b

(*s Implicit arguments synthesis errors *)

val error_occur_check : env ->  Evd.evar_map -> existential_key -> constr -> 'b

val error_not_clean :
  env ->  Evd.evar_map -> existential_key -> constr -> loc * hole_kind -> 'b

val error_unsolvable_implicit : loc -> env -> Evd.evar_map -> hole_kind -> 'b

(*s Ml Case errors *)

val error_cant_find_case_type_loc :
  loc -> env ->  Evd.evar_map -> constr -> 'b

(*s Pretyping errors *)

val error_unexpected_type_loc :
  loc -> env ->  Evd.evar_map -> constr -> constr -> 'b

val error_not_product_loc :
  loc -> env ->  Evd.evar_map -> constr -> 'b

(*s Error in conversion from AST to rawterms *)

val error_var_not_found_loc : loc -> identifier -> 'b
