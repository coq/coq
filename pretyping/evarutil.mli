
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Reduction
(*i*)

(*s This modules provides useful functions for unification modulo evars *)

val evar_env : 'a evar_info -> env

val dummy_sort : constr
type evar_constraint = conv_pb * constr * constr
type 'a evar_defs = 'a evar_map ref

val reset_problems : unit -> unit
val add_conv_pb : evar_constraint -> unit

val ise_try : 'a evar_defs -> (unit -> bool) list -> bool
val ise_undefined : 'a evar_defs -> constr -> bool
val has_undefined_isevars : 'a evar_defs -> constr -> bool

val new_isevar : 'a evar_defs -> env -> constr -> path_kind -> constr

val is_eliminator : constr -> bool
val head_is_embedded_evar : 'a evar_defs -> constr -> bool
val solve_simple_eqn :
  (env -> 'a evar_defs -> conv_pb -> constr -> constr -> bool)
  -> env -> 'a evar_defs -> conv_pb * existential * constr -> bool

(* Value/Type constraints *)

type type_constraint = constr option
type val_constraint = constr option

val empty_tycon : type_constraint
val mk_tycon : constr -> type_constraint
val empty_valcon : val_constraint
val mk_valcon : constr -> val_constraint

val split_tycon :
  Rawterm.loc -> env -> 'a evar_defs -> type_constraint -> 
    type_constraint * type_constraint

val valcon_of_tycon : type_constraint -> val_constraint

(* $Id$ *)
