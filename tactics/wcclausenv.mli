
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Environ
open Evd
open Proof_type
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

val add_prod_rel : 'a evar_map -> constr * env -> constr * env
val add_prods_rel : 'a evar_map -> constr * env -> constr * env

(*i**
val add_prod_sign : 
  'a evar_map -> constr * types signature -> constr * types signature

val add_prods_sign : 
  'a evar_map -> constr * types signature -> constr * types signature
**i*)

val res_pf_THEN : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> tactic) -> tactic

(* This behaves as [res_pf_THEN] but the tactic applied then takes
   also the subgoal number (starting from 1) as argument *)
val res_pf_THEN_i : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> int -> tactic) -> tactic

val elim_res_pf_THEN_i : 
  (wc -> tactic) -> wc clausenv -> (wc clausenv -> int -> tactic) -> tactic

val mk_clenv_using : wc -> constr -> wc clausenv

val applyUsing : constr -> tactic

val clenv_apply_n_times : int -> wc clausenv -> wc clausenv



