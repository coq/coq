
(* This modules provides useful functions for unification algorithms.
 * Used in Trad and Progmach
 * This interface will have to be improved.
 *)

open Names
open Term
open Sign
open Evd
open Environ
open Reduction

val filter_unique : 'a list -> 'a list
val distinct_id_list : identifier list -> identifier list

val filter_sign :
  ('a -> identifier * typed_type -> bool * 'a) -> var_context -> 'a ->
  'a * identifier list * var_context

val dummy_sort : constr
val do_restrict_hyps : 'a evar_map -> constr -> 'a evar_map * constr


type 'a evar_defs = 'a evar_map ref

val ise_try : 'a evar_defs -> (unit -> bool) list -> bool

val ise_undefined : 'a evar_defs -> constr -> bool
val ise_defined : 'a evar_defs -> constr -> bool

val real_clean :
  'a evar_defs ->
  section_path -> (identifier * constr) list -> constr -> constr
val new_isevar :
  unsafe_env -> 'a evar_defs -> constr -> path_kind -> constr * constr
val evar_define : 'a evar_defs -> constr -> constr -> section_path list
val solve_simple_eqn : (constr -> constr -> bool) -> 'a evar_defs ->
  (conv_pb * constr * constr) -> section_path list option

val has_undefined_isevars : 'a evar_defs -> constr -> bool
val head_is_exist : 'a evar_defs -> constr -> bool
val is_eliminator : constr -> bool
val head_is_embedded_exist : 'a evar_defs -> constr -> bool
val headconstant : constr -> section_path
val status_changed : section_path list -> conv_pb * constr * constr -> bool


(* Value/Type constraints *)

type trad_constraint = bool * (constr option * constr option)

val mt_tycon : trad_constraint
val def_vty_con : trad_constraint
val mk_tycon : constr -> trad_constraint
val mk_tycon2 : trad_constraint -> constr -> trad_constraint

(* application *)
val app_dom_tycon : 'a evar_defs -> trad_constraint -> trad_constraint
val app_rng_tycon :
  'a evar_defs -> constr -> trad_constraint -> trad_constraint

(* abstraction *)
val abs_dom_valcon : 'a evar_defs -> trad_constraint -> trad_constraint
val abs_rng_tycon : 'a evar_defs -> trad_constraint -> trad_constraint


(* $Id$ *)
