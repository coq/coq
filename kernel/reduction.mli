
(* $Id$ *)

(*i*)
open Names
open Generic
open Term
open Univ
open Environ
open Closure
open Evd
(*i*)

(* Reduction Functions. *)

exception Redelimination
exception Induc
exception Elimconst

type 'a reduction_function = 'a unsafe_env -> constr -> constr

type 'a stack_reduction_function = 
    'a unsafe_env -> constr -> constr list -> constr * constr list

val whd_stack : 'a stack_reduction_function

(*s Reduction Function Operators *)
val under_casts : 'a reduction_function -> 'a reduction_function
val strong : 'a reduction_function -> 'a reduction_function
val strong_prodspine : 'a reduction_function -> 'a reduction_function
val stack_reduction_of_reduction : 
  'a reduction_function -> 'a stack_reduction_function

(*s Generic Optimized Reduction Functions using Closures *)

(* 1. lazy strategy *)
val clos_norm_flags : Closure.flags -> 'a reduction_function
(* Same as [(strong whd_beta[delta][iota])], but much faster on big terms *) 
val nf_beta : 'a reduction_function
val nf_betaiota : 'a reduction_function
val nf_betadeltaiota : 'a reduction_function

(* 2. call by value strategy *)
val cbv_norm_flags : flags -> 'a reduction_function
val cbv_beta : 'a reduction_function
val cbv_betaiota : 'a reduction_function
val cbv_betadeltaiota : 'a reduction_function

(* 3. lazy strategy, weak head reduction *)
val whd_beta : 'a reduction_function
val whd_betaiota : 'a reduction_function
val whd_betadeltaiota : 'a reduction_function

val whd_beta_stack : 'a stack_reduction_function
val whd_betaiota_stack : 'a stack_reduction_function
val whd_betadeltaiota_stack : 'a stack_reduction_function


(*s Head normal forms *)
val whd_const_stack : section_path list -> 'a stack_reduction_function
val whd_const : section_path list -> 'a reduction_function
val whd_delta_stack : 'a stack_reduction_function
val whd_delta : 'a reduction_function
val whd_betadelta_stack : 'a stack_reduction_function
val whd_betadelta : 'a reduction_function
val whd_betadeltat_stack : 'a stack_reduction_function
val whd_betadeltat : 'a reduction_function
val whd_betadeltatiota_stack : 'a stack_reduction_function
val whd_betadeltatiota : 'a reduction_function
val whd_betadeltaiotaeta_stack : 'a stack_reduction_function
val whd_betadeltaiotaeta : 'a reduction_function

val beta_applist : (constr * constr list) -> constr


(*s Special-Purpose Reduction Functions *)
val whd_meta : 'a reduction_function
val plain_instance : 'a reduction_function
val instance : 'a reduction_function

val whd_ise : 'a reduction_function
val whd_ise1 : 'a reduction_function
val nf_ise1 : 'a reduction_function
val whd_ise1_metas : 'a reduction_function

val red_elim_const : 'a stack_reduction_function
val one_step_reduce : 'a reduction_function

val hnf_prod_app : 'c unsafe_env -> string -> constr -> constr -> constr
val hnf_prod_appvect : 
  'c unsafe_env -> string -> constr -> constr array -> constr
val hnf_prod_applist : 
  'c unsafe_env -> string -> constr -> constr list -> constr
val hnf_lam_app : 
  'c unsafe_env -> string -> constr -> constr -> constr
val hnf_lam_appvect : 
  'c unsafe_env -> string -> constr -> constr array -> constr
val hnf_lam_applist : 
  'c unsafe_env -> string -> constr -> constr list -> constr
val splay_prod : 'c unsafe_env -> constr -> (name * constr) list * constr
val decomp_prod : 'c unsafe_env -> constr -> int * constr
val decomp_n_prod : 
  'c unsafe_env -> int -> constr -> ((name * constr) list) * constr

val is_info_arity : 'c unsafe_env -> constr -> bool
val is_info_sort : 'c unsafe_env -> constr -> bool
val is_logic_arity : 'c unsafe_env -> constr -> bool
val is_type_arity : 'c unsafe_env -> constr -> bool
val is_info_cast_type : 'c unsafe_env -> constr -> bool
val contents_of_cast_type : 'c unsafe_env -> constr -> contents
val poly_args : 'a unsafe_env -> constr -> int list
val reduce_to_mind : 'c unsafe_env -> constr -> constr * constr * constr


val whd_programs : 'a reduction_function


(*s Generic reduction: reduction functions associated to tactics *)
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

val nf : 'a reduction_function
val unfoldn : 
  (int list * section_path) list -> 'a reduction_function
val fold_one_com : constr -> 'a reduction_function
val fold_commands : constr list -> 'a reduction_function
val subst_term_occ : int list -> constr -> constr -> constr
val pattern_occs : (int list * constr * constr) list -> 'a reduction_function
val hnf_constr : 'a reduction_function
val compute : 'a reduction_function
val reduction_of_redexp : red_expr -> 'a reduction_function


(*s Conversion Functions (uses closures, lazy strategy) *)

type conv_pb = 
  | CONV 
  | CONV_LEQ

val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb

type conversion_result =
  | Convertible of universes
  | NotConvertible

type conversion_test = universes -> conversion_result

val sort_cmp : conv_pb -> sorts -> sorts -> conversion_test
val base_sort_cmp : conv_pb -> sorts -> sorts -> bool

val bool_and_convert : bool -> conversion_test -> conversion_test
val convert_and : conversion_test -> conversion_test -> conversion_test
val convert_or : conversion_test -> conversion_test -> conversion_test
val convert_forall2 : 
  ('a -> 'b -> conversion_test) -> 'a array -> 'b array -> conversion_test

type 'a conversion_function = 
    'a unsafe_env -> constr -> constr -> conversion_result

val fconv : conv_pb -> 'a conversion_function

(* fconv has 2 instances:
   \begin{itemize}
   \item [conv = fconv CONV] : 
     conversion test, and adjust universes constraints
   \item [conv_leq = fconv CONV_LEQ] : cumulativity test, adjust universes
   \end{itemize} *)

val conv : 'a conversion_function
val conv_leq : 'a conversion_function

val conv_forall2 : 
  'a conversion_function -> 'a unsafe_env 
    -> constr array -> constr array -> conversion_result

val conv_forall2_i : 
  (int -> 'a conversion_function) -> 'a unsafe_env 
    -> constr array -> constr array -> conversion_result

val is_conv : 'a unsafe_env -> constr -> constr -> bool
val is_conv_leq : 'a unsafe_env -> constr -> constr -> bool

(*s Obsolete Reduction Functions *)

val hnf : 'a unsafe_env -> constr -> constr * constr list
val apprec : 'a stack_reduction_function
val red_product : 'a reduction_function
val find_mrectype : 'a unsafe_env -> constr -> constr * constr list
val find_minductype : 'a unsafe_env -> constr -> constr * constr list
val find_mcoinductype : 'a unsafe_env -> constr -> constr * constr list
val check_mrectype_spec : 'a unsafe_env -> constr -> constr
val minductype_spec : 'a unsafe_env -> constr -> constr
val mrectype_spec : 'a unsafe_env -> constr -> constr

(* Special function, which keep the key casts under Fix and MutCase. *)
val strip_all_casts : constr -> constr
