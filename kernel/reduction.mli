
(* $Id$ *)

(*i*)
open Names
(* open Generic *)
open Term
open Univ
open Evd
open Environ
open Closure
(*i*)

(* Reduction Functions. *)

exception Elimconst

(*s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time but popped with [decomp_stack]
   one by one *)

type stack
val empty_stack : stack
val append_stack : constr array -> stack -> stack
val decomp_stack : stack -> (constr * stack) option
val list_of_stack : stack -> constr list
val stack_assign : stack -> int -> constr -> stack
val stack_args_size : stack -> int
val app_stack : constr * stack -> constr

type state = constr * stack

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

val whd_stack : local_stack_reduction_function

(*s Reduction Function Operators *)

val strong : 'a reduction_function -> 'a reduction_function
val local_strong : local_reduction_function -> local_reduction_function
val strong_prodspine : local_reduction_function -> local_reduction_function
(*i
val stack_reduction_of_reduction : 
  'a reduction_function -> 'a state_reduction_function
i*)
val stacklam : (state -> 'a) -> constr list -> constr -> stack -> 'a 

(*s Generic Optimized Reduction Function using Closures *)

val clos_norm_flags : Closure.flags -> 'a reduction_function
(* Same as [(strong whd_beta[delta][iota])], but much faster on big terms *) 
val nf_beta : 'a reduction_function
val nf_betaiota : 'a reduction_function
val nf_betadeltaiota : 'a reduction_function

(* Lazy strategy, weak head reduction *)
val whd_beta : local_reduction_function
val whd_betaiota : local_reduction_function
val whd_betadeltaiota : 'a contextual_reduction_function

val whd_beta_stack : local_stack_reduction_function
val whd_betaiota_stack : local_stack_reduction_function
val whd_betadeltaiota_stack : 'a contextual_stack_reduction_function

val whd_beta_state : local_state_reduction_function
val whd_betaiota_state : local_state_reduction_function
val whd_betadeltaiota_state : 'a contextual_state_reduction_function


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
val whd_evar : 'a reduction_function

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

val poly_args : env -> 'a evar_map -> constr -> int list

val whd_programs : 'a reduction_function

(* [reduce_fix] contracts a fix redex if it is actually reducible *)

type fix_reduction_result = NotReducible | Reduced of state

val fix_recarg : fixpoint -> stack -> (int * constr) option
val reduce_fix : local_state_reduction_function -> fixpoint
   -> stack -> fix_reduction_result

(*s Conversion Functions (uses closures, lazy strategy) *)

type conv_pb = 
  | CONV 
  | CONV_LEQ

val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb

type conversion_test = constraints -> constraints

exception NotConvertible

val sort_cmp : conv_pb -> sorts -> sorts -> conversion_test
val base_sort_cmp : conv_pb -> sorts -> sorts -> bool

val bool_and_convert : bool -> conversion_test -> conversion_test
val convert_and : conversion_test -> conversion_test -> conversion_test
val convert_or : conversion_test -> conversion_test -> conversion_test
val convert_forall2 : 
  ('a -> 'b -> conversion_test) -> 'a array -> 'b array -> conversion_test

type 'a conversion_function = 
    env -> 'a evar_map -> constr -> constr -> constraints

val fconv : conv_pb -> 'a conversion_function

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

(* [whd_ise] raise [Uninstantiated_evar] if an evar remains uninstantiated; *)
(* *[whd_ise1]* is synonymous of *[whd_evar empty_env]* and *[nf_ise1]* of *)
(* *[strong whd_evar empty_env]*: they leave uninstantiated evar as it *)

val whd_ise1 : 'a evar_map -> constr -> constr
val nf_ise1 : 'a evar_map -> constr -> constr
exception Uninstantiated_evar of int
val whd_ise : 'a evar_map -> constr -> constr

(*s Obsolete Reduction Functions *)

(*i
val hnf : env -> 'a evar_map -> constr -> constr * constr list
i*)
val apprec : 'a state_reduction_function

