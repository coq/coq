
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

(* A somewhat cryptic module. *)

val pf_get_new_id  : identifier      -> goal sigma -> identifier
val pf_get_new_ids : identifier list -> goal sigma -> identifier list

type arg_binder = 
  | Dep of identifier 
  | Nodep of int 
  | Abs of int

type arg_bindings = (arg_binder * constr) list

type wc = walking_constraints

val clenv_constrain_with_bindings : arg_bindings -> wc clausenv -> wc clausenv

(*i**
val add_prod_rel : 'a evar_map -> constr * context -> constr * context

val add_prods_rel : 'a evar_map -> constr * context -> constr * context

val add_prod_sign : 
  'a evar_map -> constr * typed_type signature -> constr * typed_type signature

val add_prods_sign : 
  'a evar_map -> constr * typed_type signature -> constr * typed_type signature
**i*)

val res_pf_THEN : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> tactic) -> tactic

val res_pf_THEN_i : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> int -> tactic) -> 
    int -> tactic

val elim_res_pf_THEN_id : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> int -> tactic) -> 
    int -> tactic

val mk_clenv_using : wc -> constr -> wc clausenv

val applyUsing : constr -> tactic

val clenv_apply_n_times : int -> wc clausenv -> wc clausenv



