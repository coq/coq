(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Reduction
(*i*)

(*s This modules provides useful functions for unification modulo evars *)

val new_evar : unit -> evar
val new_evar_in_sign : env -> constr

val evar_env : 'a evar_info -> env

type 'a evar_defs
val evars_of : 'a evar_defs -> 'a evar_map
val create_evar_defs : 'a evar_map -> 'a evar_defs
val evars_reset_evd : 'a evar_map -> 'a evar_defs -> unit

type evar_constraint = conv_pb * constr * constr
val add_conv_pb : 'a evar_defs -> evar_constraint -> unit

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

val dummy_sort : constr

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
