(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Sign
open Environ
open Evd
open Evarutil
open Mod_subst
open Rawterm
open Unification

(** {6 The Type of Constructions clausale environments.} *)

type clausenv = {
  env      : env; (** the typing context *)
  evd      : evar_map; (** the mapping from metavar and evar numbers to their 
			   types and values *)
  templval : constr freelisted; (** the template which we are trying to fill 
				    out *)
  templtyp : constr freelisted (** its type *)}

(** Substitution is not applied on templenv (because [subst_clenv] is
   applied only on hints which typing env is overwritten by the
   goal env) *)
val subst_clenv : substitution -> clausenv -> clausenv

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
  ?allow_K:bool -> ?flags:unify_flags -> metavariable -> clausenv -> clausenv -> clausenv

(** {6 Unification with clenvs } *)

(** Unifies two terms in a clenv. The boolean is [allow_K] (see [Unification]) *)
val clenv_unify :
  bool -> ?flags:unify_flags -> conv_pb -> constr -> constr -> clausenv -> clausenv

(** unifies the concl of the goal with the type of the clenv *)
val clenv_unique_resolver :
  bool -> ?flags:unify_flags -> clausenv -> Goal.goal sigma -> clausenv

(** same as above ([allow_K=false]) but replaces remaining metas
   with fresh evars if [evars_flag] is [true] *)
val evar_clenv_unique_resolver :
  bool -> ?flags:unify_flags -> clausenv -> Goal.goal sigma -> clausenv

val clenv_dependent : bool -> clausenv -> metavariable list

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

(** defines metas corresponding to the name of the bindings *)
val clenv_match_args : arg_bindings -> clausenv -> clausenv

val clenv_unify_meta_types : ?flags:unify_flags -> clausenv -> clausenv

(** start with a clenv to refine with a given term with bindings *)

(** the arity of the lemma is fixed 
   the optional int tells how many prods of the lemma have to be used 
   use all of them if None *)
val make_clenv_binding_env_apply :
  env -> evar_map -> int option -> constr * constr -> constr bindings ->
   clausenv

val make_clenv_binding_apply :
  Goal.goal sigma -> int option -> constr * constr -> constr bindings ->
   clausenv
val make_clenv_binding :
  Goal.goal sigma -> constr * constr -> constr bindings -> clausenv

(** [clenv_environments sigma n t] returns [sigma',lmeta,ccl] where
   [lmetas] is a list of metas to be applied to a proof of [t] so that
   it produces the unification pattern [ccl]; [sigma'] is [sigma]
   extended with [lmetas]; if [n] is defined, it limits the size of
   the list even if [ccl] is still a product; otherwise, it stops when
   [ccl] is not a product; example: if [t] is [forall x y, x=y -> y=x]
   and [n] is [None], then [lmetas] is [Meta n1;Meta n2;Meta n3] and
   [ccl] is [Meta n1=Meta n2]; if [n] is [Some 1], [lmetas] is [Meta n1]
   and [ccl] is [forall y, Meta n1=y -> y=Meta n1] *)
val clenv_environments :
 evar_map -> int option -> types -> evar_map * constr list * types

(** [clenv_environments_evars env sigma n t] does the same but returns
   a list of Evar's defined in [env] and extends [sigma] accordingly *)
val clenv_environments_evars :
 env -> evar_map -> int option -> types -> evar_map * constr list * types

(** [clenv_conv_leq env sigma t c n] looks for c1...cn s.t. [t <= c c1...cn] *)
val clenv_conv_leq :
 env -> evar_map -> types -> constr -> int -> constr list

(** if the clause is a product, add an extra meta for this product *)
exception NotExtensibleClause
val clenv_push_prod : clausenv -> clausenv

(** {6 Pretty-print } *)
val pr_clenv : clausenv -> Pp.std_ppcmds

