(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Term
open Univ
open Evd
open Environ
open Closure
(*i*)

(* Reduction Functions. *)

exception Elimconst

type state = constr * constr stack

type 'a contextual_reduction_function = env -> 'a evar_map -> constr -> constr
type 'a reduction_function = 'a contextual_reduction_function
type local_reduction_function = constr -> constr

type 'a contextual_stack_reduction_function = 
    env -> 'a evar_map -> constr -> constr * constr list
type 'a stack_reduction_function = 'a contextual_stack_reduction_function
type local_stack_reduction_function = constr -> constr * constr list

type 'a contextual_state_reduction_function = 
    env -> 'a evar_map -> state -> state
type 'a state_reduction_function = 'a contextual_state_reduction_function
type local_state_reduction_function = state -> state

(* Removes cast and put into applicative form *)
val whd_stack : local_stack_reduction_function

(* For compatibility: alias for whd\_stack *)
val whd_castapp_stack : local_stack_reduction_function

(*s Reduction Function Operators *)

val strong : 'a reduction_function -> 'a reduction_function
val local_strong : local_reduction_function -> local_reduction_function
val strong_prodspine : local_reduction_function -> local_reduction_function
(*i
val stack_reduction_of_reduction : 
  'a reduction_function -> 'a state_reduction_function
i*)
val stacklam : (state -> 'a) -> constr list -> constr -> constr stack -> 'a 

(*s Generic Optimized Reduction Function using Closures *)

val clos_norm_flags : Closure.flags -> 'a reduction_function
(* Same as [(strong whd_beta[delta][iota])], but much faster on big terms *) 
val nf_beta : local_reduction_function
val nf_betaiota : local_reduction_function
val nf_betadeltaiota : 'a reduction_function

(* Lazy strategy, weak head reduction *)
val whd_beta : local_reduction_function
val whd_betaiota : local_reduction_function
val whd_betaiotazeta : local_reduction_function
val whd_betadeltaiota : 'a contextual_reduction_function
val whd_betadeltaiota_nolet : 'a contextual_reduction_function
val whd_betaetalet : local_reduction_function

val whd_beta_stack : local_stack_reduction_function
val whd_betaiota_stack : local_stack_reduction_function
val whd_betaiotazeta_stack : local_stack_reduction_function
val whd_betadeltaiota_stack : 'a contextual_stack_reduction_function
val whd_betadeltaiota_nolet_stack : 'a contextual_stack_reduction_function
val whd_betaetalet_stack : local_stack_reduction_function

val whd_beta_state : local_state_reduction_function
val whd_betaiota_state : local_state_reduction_function
val whd_betaiotazeta_state : local_state_reduction_function
val whd_betadeltaiota_state : 'a contextual_state_reduction_function
val whd_betadeltaiota_nolet_state : 'a contextual_state_reduction_function
val whd_betaetalet_state : local_state_reduction_function

(*s Head normal forms *)

val whd_delta_stack : 'a stack_reduction_function
val whd_delta_state : 'a state_reduction_function
val whd_delta : 'a reduction_function
val whd_betadelta_stack : 'a stack_reduction_function
val whd_betadelta_state : 'a state_reduction_function
val whd_betadelta : 'a reduction_function
val whd_betaevar_stack : 'a stack_reduction_function
val whd_betaevar_state : 'a state_reduction_function
val whd_betaevar : 'a reduction_function
val whd_betaiotaevar_stack : 'a stack_reduction_function
val whd_betaiotaevar_state : 'a state_reduction_function
val whd_betaiotaevar : 'a reduction_function
val whd_betadeltaeta_stack : 'a stack_reduction_function
val whd_betadeltaeta_state : 'a state_reduction_function
val whd_betadeltaeta : 'a reduction_function
val whd_betadeltaiotaeta_stack : 'a stack_reduction_function
val whd_betadeltaiotaeta_state : 'a state_reduction_function
val whd_betadeltaiotaeta : 'a reduction_function

val beta_applist : constr * constr list -> constr

val hnf_prod_app     : env -> 'a evar_map -> constr -> constr -> constr
val hnf_prod_appvect : env -> 'a evar_map -> constr -> constr array -> constr
val hnf_prod_applist : env -> 'a evar_map -> constr -> constr list -> constr
val hnf_lam_app      : env -> 'a evar_map -> constr -> constr -> constr
val hnf_lam_appvect  : env -> 'a evar_map -> constr -> constr array -> constr
val hnf_lam_applist  : env -> 'a evar_map -> constr -> constr list -> constr

val splay_prod : env -> 'a evar_map -> constr -> (name * constr) list * constr
val splay_arity : env -> 'a evar_map -> constr -> (name * constr) list * sorts
val sort_of_arity : env -> constr -> sorts
val decomp_n_prod : 
  env -> 'a evar_map -> int -> constr -> Sign.rel_context * constr
val splay_prod_assum :
  env -> 'a evar_map -> constr -> Sign.rel_context * constr

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)

val reducible_mind_case : constr -> bool
val reduce_mind_case : constr miota_args -> constr

val is_arity : env -> 'a evar_map -> constr -> bool
val is_info_type : env -> 'a evar_map -> unsafe_type_judgment -> bool
val is_info_arity : env -> 'a evar_map -> constr -> bool
(*i Pour l'extraction
val is_type_arity : env -> 'a evar_map -> constr -> bool
val is_info_cast_type : env -> 'a evar_map -> constr -> bool
val contents_of_cast_type : env -> 'a evar_map -> constr -> contents
i*)

val whd_programs : 'a reduction_function

(* [reduce_fix] contracts a fix redex if it is actually reducible *)

type fix_reduction_result = NotReducible | Reduced of state

val fix_recarg : fixpoint -> constr stack -> (int * constr) option
val reduce_fix : local_state_reduction_function -> fixpoint
   -> constr stack -> fix_reduction_result

(*s Conversion Functions (uses closures, lazy strategy) *)

type conversion_test = constraints -> constraints

exception NotConvertible

type conv_pb = 
  | CONV 
  | CUMUL

val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb

val sort_cmp : conv_pb -> sorts -> sorts -> conversion_test
val base_sort_cmp : conv_pb -> sorts -> sorts -> bool

type 'a conversion_function = 
    env -> 'a evar_map -> constr -> constr -> constraints

(* [fconv] has 2 instances: [conv = fconv CONV] i.e. conversion test, and
   [conv_leq = fconv CONV_LEQ] i.e. cumulativity test. *)

val conv : 'a conversion_function
val conv_leq : 'a conversion_function

val conv_forall2 : 
  'a conversion_function -> env -> 'a evar_map -> constr array 
    -> constr array -> constraints

val conv_forall2_i : 
  (int -> 'a conversion_function) -> env -> 'a evar_map
    -> constr array -> constr array -> constraints

val is_conv : env -> 'a evar_map -> constr -> constr -> bool
val is_conv_leq : env -> 'a evar_map -> constr -> constr -> bool
val is_fconv : conv_pb -> env -> 'a evar_map -> constr -> constr -> bool

(*s Special-Purpose Reduction Functions *)

val whd_meta : (int * constr) list -> constr -> constr
val plain_instance : (int * constr) list -> constr -> constr
val instance : (int * constr) list -> constr -> constr

(*s Obsolete Reduction Functions *)

(*i
val hnf : env -> 'a evar_map -> constr -> constr * constr list
i*)
val apprec : 'a state_reduction_function

