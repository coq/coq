(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Univ
open Evd
open Environ
open Closure
(*i*)

(* Reduction Functions. *)

exception Elimconst

(************************************************************************)
(*s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type 'a stack_member =
  | Zapp of 'a list
  | Zcase of case_info * 'a * 'a array
  | Zfix of 'a * 'a stack
  | Zshift of int
  | Zupdate of 'a

and 'a stack = 'a stack_member list

val empty_stack : 'a stack
val append_stack : 'a array -> 'a stack -> 'a stack
val append_stack_list : 'a list -> 'a stack -> 'a stack

val decomp_stack : 'a stack -> ('a * 'a stack) option
val list_of_stack : 'a stack -> 'a list
val array_of_stack : 'a stack -> 'a array
val stack_assign : 'a stack -> int -> 'a -> 'a stack
val stack_args_size : 'a stack -> int
val app_stack : constr * constr stack -> constr
val stack_tail : int -> 'a stack -> 'a stack
val stack_nth : 'a stack -> int -> 'a

(************************************************************************)

type state = constr * constr stack

type contextual_reduction_function = env -> evar_map -> constr -> constr
type reduction_function = contextual_reduction_function
type local_reduction_function = evar_map -> constr -> constr

type contextual_stack_reduction_function =
    env -> evar_map -> constr -> constr * constr list
type stack_reduction_function = contextual_stack_reduction_function
type local_stack_reduction_function =
    evar_map -> constr -> constr * constr list

type contextual_state_reduction_function =
    env -> evar_map -> state -> state
type state_reduction_function = contextual_state_reduction_function
type local_state_reduction_function = evar_map -> state -> state

(* Removes cast and put into applicative form *)
val whd_stack : local_stack_reduction_function

(* For compatibility: alias for whd\_stack *)
val whd_castapp_stack : local_stack_reduction_function

(*s Reduction Function Operators *)

val strong : reduction_function -> reduction_function
val local_strong : local_reduction_function -> local_reduction_function
val strong_prodspine : local_reduction_function -> local_reduction_function
(*i
val stack_reduction_of_reduction :
  'a reduction_function -> 'a state_reduction_function
i*)
val stacklam : (state -> 'a) -> constr list -> constr -> constr stack -> 'a

(*s Generic Optimized Reduction Function using Closures *)

val clos_norm_flags : Closure.RedFlags.reds -> reduction_function
(* Same as [(strong whd_beta[delta][iota])], but much faster on big terms *)
val nf_beta : local_reduction_function
val nf_betaiota : local_reduction_function
val nf_betadeltaiota : reduction_function
val nf_evar : evar_map -> constr -> constr

val nf_betaiota_preserving_vm_cast : reduction_function
(* Lazy strategy, weak head reduction *)
val whd_evar :  evar_map -> constr -> constr
val whd_beta : local_reduction_function
val whd_betaiota : local_reduction_function
val whd_betaiotazeta : local_reduction_function
val whd_betadeltaiota :  contextual_reduction_function
val whd_betadeltaiota_nolet :  contextual_reduction_function
val whd_betaetalet : local_reduction_function
val whd_betalet : local_reduction_function

val whd_beta_stack : local_stack_reduction_function
val whd_betaiota_stack : local_stack_reduction_function
val whd_betaiotazeta_stack : local_stack_reduction_function
val whd_betadeltaiota_stack : contextual_stack_reduction_function
val whd_betadeltaiota_nolet_stack : contextual_stack_reduction_function
val whd_betaetalet_stack : local_stack_reduction_function
val whd_betalet_stack : local_stack_reduction_function

val whd_beta_state : local_state_reduction_function
val whd_betaiota_state : local_state_reduction_function
val whd_betaiotazeta_state : local_state_reduction_function
val whd_betadeltaiota_state : contextual_state_reduction_function
val whd_betadeltaiota_nolet_state : contextual_state_reduction_function
val whd_betaetalet_state : local_state_reduction_function
val whd_betalet_state : local_state_reduction_function

(*s Head normal forms *)

val whd_delta_stack :  stack_reduction_function
val whd_delta_state :  state_reduction_function
val whd_delta :  reduction_function
val whd_betadelta_stack :  stack_reduction_function
val whd_betadelta_state :  state_reduction_function
val whd_betadelta :  reduction_function
val whd_betadeltaeta_stack :  stack_reduction_function
val whd_betadeltaeta_state :  state_reduction_function
val whd_betadeltaeta :  reduction_function
val whd_betadeltaiotaeta_stack :  stack_reduction_function
val whd_betadeltaiotaeta_state :  state_reduction_function
val whd_betadeltaiotaeta :  reduction_function

val whd_eta : constr -> constr
val whd_zeta : constr -> constr

(* Various reduction functions *)

val safe_evar_value : evar_map -> existential -> constr option

val beta_applist : constr * constr list -> constr

val hnf_prod_app     : env ->  evar_map -> constr -> constr -> constr
val hnf_prod_appvect : env ->  evar_map -> constr -> constr array -> constr
val hnf_prod_applist : env ->  evar_map -> constr -> constr list -> constr
val hnf_lam_app      : env ->  evar_map -> constr -> constr -> constr
val hnf_lam_appvect  : env ->  evar_map -> constr -> constr array -> constr
val hnf_lam_applist  : env ->  evar_map -> constr -> constr list -> constr

val splay_prod : env ->  evar_map -> constr -> (name * constr) list * constr
val splay_lam : env ->  evar_map -> constr -> (name * constr) list * constr
val splay_arity : env ->  evar_map -> constr -> (name * constr) list * sorts
val sort_of_arity : env -> constr -> sorts
val splay_prod_n : env ->  evar_map -> int -> constr -> rel_context * constr
val splay_lam_n : env ->  evar_map -> int -> constr -> rel_context * constr
val splay_prod_assum :
  env ->  evar_map -> constr -> rel_context * constr
val decomp_sort : env -> evar_map -> types -> sorts
val is_sort : env -> evar_map -> types -> bool

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)

val reducible_mind_case : constr -> bool
val reduce_mind_case : constr miota_args -> constr

val find_conclusion : env -> evar_map -> constr -> (constr,constr) kind_of_term
val is_arity : env ->  evar_map -> constr -> bool

val whd_programs :  reduction_function

(* [reduce_fix redfun fix stk] contracts [fix stk] if it is actually
   reducible; the structural argument is reduced by [redfun] *)

type fix_reduction_result = NotReducible | Reduced of state

val fix_recarg : fixpoint -> constr stack -> (int * constr) option
val reduce_fix : local_state_reduction_function -> evar_map -> fixpoint
   -> constr stack -> fix_reduction_result

(*s Querying the kernel conversion oracle: opaque/transparent constants *)
val is_transparent : 'a tableKey -> bool

(*s Conversion Functions (uses closures, lazy strategy) *)

type conversion_test = constraints -> constraints

val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb

val sort_cmp : conv_pb -> sorts -> sorts -> conversion_test

val is_conv : env ->  evar_map -> constr -> constr -> bool
val is_conv_leq : env ->  evar_map -> constr -> constr -> bool
val is_fconv : conv_pb -> env ->  evar_map -> constr -> constr -> bool

val is_trans_conv : transparent_state -> env -> evar_map -> constr -> constr -> bool
val is_trans_conv_leq : transparent_state -> env ->  evar_map -> constr -> constr -> bool
val is_trans_fconv : conv_pb -> transparent_state -> env ->  evar_map -> constr -> constr -> bool

(*s Special-Purpose Reduction Functions *)

val whd_meta : evar_map -> constr -> constr
val plain_instance : (metavariable * constr) list -> constr -> constr
val instance :evar_map -> (metavariable * constr) list -> constr -> constr
val head_unfold_under_prod : transparent_state -> reduction_function

(*s Heuristic for Conversion with Evar *)

val whd_betaiota_deltazeta_for_iota_state :  state_reduction_function

(*s Meta-related reduction functions *)
val meta_instance : evar_map -> constr freelisted -> constr
val nf_meta       : evar_map -> constr -> constr
val meta_reducible_instance : evar_map -> constr freelisted -> constr
