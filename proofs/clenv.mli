(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Environ
open Evd
open Mod_subst
open Unification
open Misctypes

(** {6 The Type of Constructions clausale environments.} *)

type clausenv = {
  env      : env; (** the typing context *)
  evd      : evar_map; (** the mapping from metavar and evar numbers to their 
			   types and values *)
  templval : constr freelisted; (** the template which we are trying to fill 
				    out *)
  templtyp : constr freelisted (** its type *)}

(** subject of clenv (instantiated) *)
val clenv_value     : clausenv -> constr

(** type of clenv (instantiated) *)
val clenv_type      : clausenv -> types

(** substitute resolved metas *)
val clenv_nf_meta   : clausenv -> constr -> constr

(** type of a meta in clenv context *)
val clenv_meta_type : clausenv -> metavariable -> types

val mk_clenv_from : Goal.goal sigma -> constr * types -> clausenv
val mk_clenv_from_n :
  Goal.goal sigma -> int option -> constr * types -> clausenv
val mk_clenv_type_of : Goal.goal sigma -> constr -> clausenv
val mk_clenv_from_env : env -> evar_map -> int option -> constr * types -> clausenv

(** {6 linking of clenvs } *)

val connect_clenv : Goal.goal sigma -> clausenv -> clausenv
val clenv_fchain :
  ?flags:unify_flags -> metavariable -> clausenv -> clausenv -> clausenv

(** {6 Unification with clenvs } *)

(** Unifies two terms in a clenv. The boolean is [allow_K] (see [Unification]) *)
val clenv_unify :
  ?flags:unify_flags -> conv_pb -> constr -> constr -> clausenv -> clausenv

(** unifies the concl of the goal with the type of the clenv *)
val clenv_unique_resolver :
  ?flags:unify_flags -> clausenv -> Goal.goal sigma -> clausenv

val clenv_dependent : clausenv -> metavariable list

val clenv_pose_metas_as_evars : clausenv -> metavariable list -> clausenv

(** {6 Bindings } *)

type arg_bindings = constr explicit_bindings

(** bindings where the key is the position in the template of the
   clenv (dependent or not). Positions can be negative meaning to
   start from the rightmost argument of the template. *)
val clenv_independent : clausenv -> metavariable list
val clenv_missing : clausenv -> metavariable list

(** for the purpose of inversion tactics *)
exception NoSuchBinding
val clenv_constrain_last_binding : constr -> clausenv -> clausenv

val clenv_unify_meta_types : ?flags:unify_flags -> clausenv -> clausenv

(** start with a clenv to refine with a given term with bindings *)

(** the arity of the lemma is fixed 
   the optional int tells how many prods of the lemma have to be used 
   use all of them if None *)
val make_clenv_binding_env_apply :
  env -> evar_map -> int option -> constr * constr -> constr bindings ->
   clausenv

val make_clenv_binding_apply :
  env -> evar_map -> int option -> constr * constr -> constr bindings ->
   clausenv
val make_clenv_binding :
  env -> evar_map -> constr * constr -> constr bindings -> clausenv

(** if the clause is a product, add an extra meta for this product *)
exception NotExtensibleClause
val clenv_push_prod : clausenv -> clausenv

(** {6 Pretty-print (debug only) } *)
val pr_clenv : clausenv -> Pp.std_ppcmds

