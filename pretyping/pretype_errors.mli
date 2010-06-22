(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Sign
open Environ
open Rawterm
open Inductiveops

(** {6 The type of errors raised by the pretyper } *)

type pretype_error =
  (** Old Case *)
  | CantFindCaseType of constr
  (** Unification *)
  | OccurCheck of existential_key * constr
  | NotClean of existential_key * constr * Evd.hole_kind
  | UnsolvableImplicit of Evd.evar_info * Evd.hole_kind *
      Evd.unsolvability_explanation option
  | CannotUnify of constr * constr
  | CannotUnifyLocal of constr * constr * constr
  | CannotUnifyBindingType of constr * constr
  | CannotGeneralize of constr
  | NoOccurrenceFound of constr * identifier option
  | CannotFindWellTypedAbstraction of constr * constr list
  | AbstractionOverMeta of name * name
  | NonLinearUnification of name * constr
  (** Pretyping *)
  | VarNotFound of identifier
  | UnexpectedType of constr * constr
  | NotProduct of constr

exception PretypeError of env * pretype_error

val precatchable_exception : exn -> bool

(** Presenting terms without solved evars *)
val nf_evar :  Evd.evar_map -> constr -> constr
val j_nf_evar :  Evd.evar_map -> unsafe_judgment -> unsafe_judgment
val jl_nf_evar :
   Evd.evar_map -> unsafe_judgment list -> unsafe_judgment list
val jv_nf_evar :
   Evd.evar_map -> unsafe_judgment array -> unsafe_judgment array
val tj_nf_evar :
   Evd.evar_map -> unsafe_type_judgment -> unsafe_type_judgment


(** Raising errors *)
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

val error_not_a_type_loc :
  loc -> env -> Evd.evar_map -> unsafe_judgment -> 'b

val error_cannot_coerce : env -> Evd.evar_map -> constr * constr -> 'b

(** {6 Implicit arguments synthesis errors } *)

val error_occur_check : env ->  Evd.evar_map -> existential_key -> constr -> 'b

val error_not_clean :
  env -> Evd.evar_map -> existential_key -> constr -> loc * Evd.hole_kind -> 'b

val error_unsolvable_implicit :
  loc -> env -> Evd.evar_map -> Evd.evar_info -> Evd.hole_kind ->
      Evd.unsolvability_explanation option -> 'b

val error_cannot_unify : env -> Evd.evar_map -> constr * constr -> 'b

val error_cannot_unify_local : env -> Evd.evar_map -> constr * constr * constr -> 'b

val error_cannot_find_well_typed_abstraction : env -> Evd.evar_map ->
      constr -> constr list -> 'b

val error_abstraction_over_meta : env -> Evd.evar_map ->
  metavariable -> metavariable -> 'b

val error_non_linear_unification : env -> Evd.evar_map ->
  metavariable -> constr -> 'b

(** {6 Ml Case errors } *)

val error_cant_find_case_type_loc :
  loc -> env ->  Evd.evar_map -> constr -> 'b

(** {6 Pretyping errors } *)

val error_unexpected_type_loc :
  loc -> env ->  Evd.evar_map -> constr -> constr -> 'b

val error_not_product_loc :
  loc -> env ->  Evd.evar_map -> constr -> 'b

(** {6 Error in conversion from AST to rawterms } *)

val error_var_not_found_loc : loc -> identifier -> 'b
