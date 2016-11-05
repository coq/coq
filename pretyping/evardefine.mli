(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Evd
open Environ

val env_nf_evar : evar_map -> env -> env
val env_nf_betaiotaevar : evar_map -> env -> env

type type_constraint = types option
type val_constraint = constr option

val empty_tycon : type_constraint
val mk_tycon : EConstr.constr -> type_constraint
val empty_valcon : val_constraint
val mk_valcon : EConstr.constr -> val_constraint

(** Instantiate an evar by as many lambda's as needed so that its arguments
    are moved to the evar substitution (i.e. turn [?x[vars1:=args1] args] into
    [?y[vars1:=args1,vars:=args]] with
    [vars1 |- ?x:=\vars.?y[vars1:=vars1,vars:=vars]] *)
val evar_absorb_arguments : env -> evar_map -> EConstr.existential -> EConstr.constr list ->
  evar_map * existential

val split_tycon :
  Loc.t -> env ->  evar_map -> type_constraint ->
    evar_map * (Name.t * type_constraint * type_constraint)

val valcon_of_tycon : type_constraint -> val_constraint
val lift_tycon : int -> type_constraint -> type_constraint

val define_evar_as_product : evar_map -> EConstr.existential -> evar_map * EConstr.types
val define_evar_as_lambda : env -> evar_map -> EConstr.existential -> evar_map * EConstr.types
val define_evar_as_sort : env -> evar_map -> EConstr.existential -> evar_map * sorts

(** {6 debug pretty-printer:} *)

val pr_tycon : env -> type_constraint -> Pp.std_ppcmds

