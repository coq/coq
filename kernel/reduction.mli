
(* $Id$ *)

open Names
open Generic
open Term
open Univ
open Environ
open Closure
open Evd

exception Redelimination
exception Induc
exception Elimconst

type 'a reduction_function = 'a unsafe_env -> constr -> constr
type 'a stack_reduction_function = 'a unsafe_env -> constr -> constr list 
  -> constr * constr list

val whd_stack : 'a stack_reduction_function

(* Reduction Function Operators *)
val under_casts      : 'a reduction_function -> 'a reduction_function
val strong           : 'a reduction_function -> 'a reduction_function
val strong_prodspine : 'a reduction_function -> 'a reduction_function
val stack_reduction_of_reduction : 
  'a reduction_function -> 'a stack_reduction_function

(*************************
 ** Reduction Functions **
 *************************)

(* Generic Optimized Reduction Functions using Closures *)

(* 1. lazy strategy *)
val clos_norm_flags : Closure.flags -> 'c unsafe_env -> 'a reduction_function
(* Same as (strong whd_beta[delta][iota]), but much faster on big terms *) 
val nf_beta : 'a reduction_function
val nf_betaiota : 'a reduction_function
val nf_betadeltaiota : 'c unsafe_env -> 'a reduction_function

(* 2. call by value strategy *)
val cbv_norm_flags : flags -> 'c unsafe_env -> 'a reduction_function
val cbv_beta : 'a reduction_function
val cbv_betaiota : 'a reduction_function
val cbv_betadeltaiota : 'c unsafe_env -> 'a reduction_function

(* 3. lazy strategy, weak head reduction *)
val whd_beta : 'a reduction_function
val whd_betaiota : 'a reduction_function
val whd_betadeltaiota : 'c unsafe_env -> 'a reduction_function

val whd_beta_stack : 'a stack_reduction_function
val whd_betaiota_stack : 'a stack_reduction_function
val whd_betadeltaiota_stack : 'c unsafe_env -> 'a stack_reduction_function


(* Head normal forms *)
val whd_const_stack : section_path list -> 'c unsafe_env -> 'a stack_reduction_function
val whd_const : section_path list -> 'c unsafe_env -> 'a reduction_function
val whd_delta_stack : 'c unsafe_env -> 'a stack_reduction_function
val whd_delta : 'c unsafe_env -> 'a reduction_function
val whd_betadelta_stack : 'c unsafe_env -> 'a stack_reduction_function
val whd_betadelta : 'c unsafe_env -> 'a reduction_function
val whd_betadeltat_stack : 'c unsafe_env -> 'a stack_reduction_function
val whd_betadeltat : 'c unsafe_env -> 'a reduction_function
val whd_betadeltatiota_stack : 'c unsafe_env -> 'a stack_reduction_function
val whd_betadeltatiota : 'c unsafe_env -> 'a reduction_function
val whd_betadeltaiotaeta_stack : 'c unsafe_env -> 'a stack_reduction_function
val whd_betadeltaiotaeta : 'c unsafe_env -> 'a reduction_function

val beta_applist : (constr * constr list) -> constr


(* Special-Purpose Reduction Functions *)
val whd_meta : (int * constr) list -> 'a reduction_function
val plain_instance : (int * constr) list -> 'a reduction_function
val instance : (int * constr) list -> 'a reduction_function

val whd_ise : 'a unsafe_env -> 'a reduction_function
val whd_ise1 : 'a unsafe_env -> 'a reduction_function
val nf_ise1 : 'a unsafe_env -> 'a reduction_function
val whd_ise1_metas : 'a unsafe_env -> 'a reduction_function

val red_elim_const : 'c unsafe_env -> 'a stack_reduction_function
val one_step_reduce : 'c unsafe_env -> constr -> constr

val hnf_prod_app : 'c unsafe_env -> string -> constr -> constr -> constr
val hnf_prod_appvect : 
  'c unsafe_env -> string -> constr -> constr array -> constr
val hnf_prod_applist : 'c unsafe_env -> string -> constr -> constr list -> constr
val hnf_lam_app : 'c unsafe_env -> string -> constr -> constr -> constr
val hnf_lam_appvect : 'c unsafe_env -> string -> constr -> constr array -> constr
val hnf_lam_applist : 'c unsafe_env -> string -> constr -> constr list -> constr
val splay_prod : 'c unsafe_env -> constr -> (name * constr) list * constr
val decomp_prod : 'c unsafe_env -> constr -> int * constr
val decomp_n_prod : 
  'c unsafe_env -> int -> constr -> ((name * constr) list) * constr

val is_info_arity : 'c unsafe_env -> constr -> bool
val is_info_sort : constr -> bool
val is_logic_arity : 'c unsafe_env -> constr -> bool
val is_type_arity : 'c unsafe_env -> constr -> bool
val is_info_cast_type : 'c unsafe_env -> constr -> bool
val contents_of_cast_type : 'c unsafe_env -> constr -> contents
val poly_args : constr -> int list
val reduce_to_mind : 'c unsafe_env -> constr -> constr * constr * constr
val reduce_to_ind  : 'c unsafe_env -> constr -> 
                                section_path*constr*constr

val whd_programs : 'a reduction_function

(* Generic reduction: reduction functions associated to tactics *)
type red_expr =
  | Red
  | Hnf
  | Simpl
  | Cbv of flags
  | Lazy of flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Change of constr
  | Pattern of (int list * constr * constr) list


val nf : 'c unsafe_env -> 'a reduction_function
val unfoldn : 
  (int list * section_path) list -> 'c unsafe_env -> 'a reduction_function
val fold_one_com : 'c unsafe_env -> constr -> 'a reduction_function
val fold_commands : constr list -> 'c unsafe_env -> 'a reduction_function
val subst_term_occ : int list -> constr -> constr -> constr
val pattern_occs : (int list * constr * constr) list -> constr -> constr
val hnf_constr : 'c unsafe_env -> constr -> constr
val compute : 'c unsafe_env -> 'a reduction_function
val reduction_of_redexp : red_expr -> 'c unsafe_env -> constr -> constr



(* Conversion Functions (uses closures, lazy strategy) *)

type 'a conversion_function = 
    'a unsafe_env -> constr -> constr -> bool * universes

val fconv : conv_pb -> 'a conversion_function
(* fconv has 4 instances:
 * conv   = fconv CONV   : conversion test, and adjust universes constraints
 * conv_x = fconv CONV_X :     id.        , without adjusting univ 
     (used in tactics)
 * conv_leq   = fconv CONV_LEQ   : cumulativity test, adjust universes
 * conv_x_leq = fconv CONV_X_LEQ :       id.        , without adjusting 
     (in tactics)
 *)
val conv : 'a conversion_function
val conv_leq : 'a conversion_function
val conv_x : 'a conversion_function
val conv_x_leq : 'a conversion_function

(* Obsolete Reduction Functions *)

val hnf : 'a unsafe_env -> constr -> constr * constr list
val apprec : 'a stack_reduction_function
val red_product : 'a reduction_function
val find_mrectype : 'a unsafe_env -> constr -> constr * constr list
val find_minductype : 'a unsafe_env -> constr -> constr * constr list
val find_mcoinductype : 'a unsafe_env -> constr -> constr * constr list
val check_mrectype_spec : 'a unsafe_env -> constr -> constr
val minductype_spec : 'a unsafe_env -> constr -> constr
val mrectype_spec : 'a unsafe_env -> constr -> constr

(* Fonction spéciale qui laisse les cast clés sous les Fix ou les MutCase *)
val strip_all_casts : constr -> constr
