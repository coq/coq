
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Proof_trees
open Tacmach
open Clenv
(*i*)

val pf_get_new_id  : identifier      -> goal sigma -> identifier
val pf_get_new_ids : identifier list -> goal sigma -> identifier list

type arg_binder = 
  | Dep of identifier 
  | Nodep of int 
  | Abs of int

type arg_bindings = (arg_binder * constr) list

val clenv_constrain_with_bindings :
  arg_bindings -> walking_constraints clausenv -> walking_constraints clausenv

val add_prod_rel : 'a evar_map -> constr * context -> constr * context

val add_prods_rel : 'a evar_map -> constr * context -> constr * context

val add_prod_sign : 
  'a evar_map -> constr * typed_type signature -> constr * typed_type signature

val add_prods_sign : 
  'a evar_map -> constr * typed_type signature -> constr * typed_type signature

val res_pf_THEN         : (walking_constraints -> tactic) -> 
                           walking_constraints clausenv -> 
                          (walking_constraints clausenv -> tactic) -> tactic

val res_pf_THEN_i       : (walking_constraints -> tactic) -> 
                           walking_constraints clausenv -> 
                          (walking_constraints clausenv -> int -> tactic) -> 
                           int -> tactic

val elim_res_pf_THEN_i  : (walking_constraints -> tactic) -> 
                           walking_constraints clausenv -> 
                          (walking_constraints clausenv -> int -> tactic) -> 
                            int -> tactic

val mk_clenv_using      : walking_constraints -> constr -> 
                                     walking_constraints clausenv

val applyUsing          : constr -> tactic

val clenv_apply_n_times : int -> walking_constraints clausenv -> 
                          walking_constraints clausenv


