(* $Id$ *)

(*i*)
open Names
open Sign
open Univ
open Term
open Evd
open Environ
(*i*)


(* Basic operations of the typing machine. *)

val make_judge : constr -> typed_type -> unsafe_judgment

val j_val_only : unsafe_judgment -> constr

(* If [j] is the judgement $c:t:s$, then [typed_type_of_judgment env j]
   constructs the typed type $t:s$, while [assumption_of_judgement env j]
   cosntructs the type type $c:t$, checking that $t$ is a sort. *)

val typed_type_of_judgment : 
  env -> 'a evar_map -> unsafe_judgment -> typed_type
val assumption_of_judgment : 
  env -> 'a evar_map -> unsafe_judgment -> typed_type

val relative : env -> int -> unsafe_judgment

val type_of_constant : env -> 'a evar_map -> constant -> typed_type

val type_of_inductive : env -> 'a evar_map -> inductive -> typed_type

val type_of_constructor : env -> 'a evar_map -> constructor -> constr

val type_of_existential : env -> 'a evar_map -> constr -> constr

val type_of_case : env -> 'a evar_map -> case_info
  -> unsafe_judgment -> unsafe_judgment 
    -> unsafe_judgment array -> unsafe_judgment

val type_case_branches :
  env -> 'a evar_map -> constr -> constr -> constr -> constr 
    -> constr * constr array * constr 

val judge_of_prop_contents : contents -> unsafe_judgment

val judge_of_type : universe -> unsafe_judgment * constraints

val abs_rel : 
  env -> 'a evar_map -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * constraints

val gen_rel :
  env -> 'a evar_map -> name -> typed_type -> unsafe_judgment 
    -> unsafe_judgment * constraints

val sort_of_product_without_univ : sorts -> sorts -> sorts

val cast_rel : 
  env -> 'a evar_map -> unsafe_judgment -> unsafe_judgment 
    -> unsafe_judgment

val apply_rel_list : 
  env -> 'a evar_map -> bool -> unsafe_judgment list -> unsafe_judgment
    -> unsafe_judgment * constraints

val check_fix : env -> 'a evar_map -> constr -> unit
val check_cofix : env -> 'a evar_map -> constr -> unit
val control_only_guard : env -> 'a evar_map -> constr -> unit

val type_fixpoint : env -> 'a evar_map -> name list -> typed_type array 
    -> unsafe_judgment array -> constraints

val type_one_branch_dep : env -> 'a evar_map -> 
  int * constr list * constr -> constr -> constr -> constr 

val type_one_branch_nodep : env -> 'a evar_map -> 
  int * constr list * constr -> constr -> constr 

val make_arity_dep : 
  env -> 'a evar_map -> constr -> constr -> constr -> constr 

val make_arity_nodep : 
  env -> 'a evar_map -> constr -> constr -> constr 

val find_case_dep_nparams :
  env -> 'a evar_map -> constr * constr ->
    inductive * constr list ->
      constr -> bool * (int * constr list * constr list) 

(* The constr list is the global args list *)
val type_inst_construct :
  env -> 'a evar_map -> int -> inductive * constr list -> constr 

val hyps_inclusion : env -> 'a evar_map -> var_context -> var_context -> bool

val keep_hyps : var_context -> Idset.t -> var_context
