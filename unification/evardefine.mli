(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Evd
open Environ

val env_nf_evar : evar_map -> env -> env
val env_nf_betaiotaevar : evar_map -> env -> env

type type_constraint = types option
type val_constraint = constr option

val empty_tycon : type_constraint
val mk_tycon : constr -> type_constraint
val empty_valcon : val_constraint
val mk_valcon : constr -> val_constraint

(** Instantiate an evar by as many lambda's as needed so that its arguments
    are moved to the evar substitution (i.e. turn [?x[vars1:=args1] args] into
    [?y[vars1:=args1,vars:=args]] with
    [vars1 |- ?x:=\vars.?y[vars1:=vars1,vars:=vars]] *)
val evar_absorb_arguments : env -> evar_map -> existential -> constr list ->
  evar_map * existential

val split_as_array : env -> evar_map -> type_constraint ->
  evar_map * type_constraint
(** If the constraint can be made to look like [array A] return [A],
   otherwise return [None] (this makes later coercion possible). *)

val valcon_of_tycon : type_constraint -> val_constraint
val lift_tycon : int -> type_constraint -> type_constraint

val define_evar_as_product : env -> evar_map -> existential -> evar_map * types
val define_evar_as_lambda : env -> evar_map -> existential -> evar_map * types
val define_evar_as_sort : env -> evar_map -> existential -> evar_map * Sorts.t

(** {6 debug pretty-printer:} *)

val pr_tycon : env -> evar_map -> type_constraint -> Pp.t

(** Used for bidi heuristic when typing lambdas. Transforms an applied
    evar to an evar with bigger context (ie ?X e to ?X'@{y=e}). *)
val presplit : env -> evar_map -> EConstr.t -> evar_map * EConstr.t
