(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd
open Names
open Environ
open EConstr
open Glob_term

(** {6 Coercions. } *)

type coercion_trace

val empty_coercion_trace : coercion_trace

val reapply_coercions : evar_map -> coercion_trace -> EConstr.t -> EConstr.t

(** [inh_coerce_to_sort env isevars j] coerces [j] to a type; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type a sort; it fails if no coercion is applicable *)
val inh_coerce_to_sort : ?loc:Loc.t -> ?use_coercions:bool ->
  env -> evar_map -> unsafe_judgment -> evar_map * unsafe_type_judgment

(** [inh_coerce_to_base env isevars j] coerces [j] to its base type; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type its base type (the notion depends on the coercion system) *)
val inh_coerce_to_base : ?loc:Loc.t -> program_mode:bool ->
  env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

(** [remove_subset env sigma t] applies program mode transformations
   to [t], recursively transforming [{x : A | P}] into [A] *)
val remove_subset : env -> evar_map -> types -> types

(** [inh_conv_coerce_to resolve_tc Loc.t env isevars j t] coerces [j] to an
    object of type [t]; i.e. it inserts a coercion into [j], if needed, in such
    a way [t] and [j.uj_type] are convertible; it fails if no coercion is
    applicable. resolve_tc=false disables resolving type classes (as the last
    resort before failing) *)

val inh_conv_coerce_to : ?loc:Loc.t -> program_mode:bool -> resolve_tc:bool ->
  ?use_coercions:bool -> ?patvars_abstract:bool -> env -> evar_map -> ?flags:Evarconv.unify_flags ->
  unsafe_judgment -> types -> evar_map * unsafe_judgment * coercion_trace option

val inh_conv_coerce_rigid_to : ?loc:Loc.t -> program_mode:bool -> resolve_tc:bool ->
  ?use_coercions:bool -> ?patvars_abstract:bool -> env -> evar_map -> ?flags:Evarconv.unify_flags ->
  unsafe_judgment -> types -> evar_map * unsafe_judgment * coercion_trace option

(** [inh_pattern_coerce_to loc env isevars pat ind1 ind2] coerces the Cases
    pattern [pat] typed in [ind1] into a pattern typed in [ind2];
    raises [Not_found] if no coercion found *)
val inh_pattern_coerce_to :
  ?loc:Loc.t -> env -> cases_pattern -> inductive -> inductive -> cases_pattern

type expected = Type of types | Sort | Product

type hook = env -> evar_map -> flags:Evarconv.unify_flags -> constr ->
  inferred:types -> expected:expected -> (evar_map * constr * constr) option

(** A plugin can override the coercion mechanism by registering a hook here.
    Note that these hooks will only be trigerred when no direct or reversible
    coercion applies.
    Newly registered hooks are not active by default, see [activate_hook] below.
    The same hook cannot be registered twice, except if [override] is [true].
    Beware that this addition is not persistent, it is up to the plugin to use
    libobject if needed. *)
val register_hook : name:string -> ?override:bool -> hook -> unit

(** Activate a previously registered hook.
    Most recently activated hooks are tried first. *)
val activate_hook : name:string -> unit

(** Deactivate a hook. If the hook wasn't registered/active,
    this does nothing. *)
val deactivate_hook : name:string -> unit

type delayed_app_body

val start_app_body : evar_map -> constr -> delayed_app_body

val push_arg : delayed_app_body -> constr -> delayed_app_body

val force_app_body : delayed_app_body -> constr

val reapply_coercions_body : evar_map -> coercion_trace -> delayed_app_body -> delayed_app_body

(** [inh_app_fun resolve_tc env isevars j] coerces [j] to a function; i.e. it
    inserts a coercion into [j], if needed, in such a way it gets as
    type a product; it returns [j] if no coercion is applicable.
    resolve_tc=false disables resolving type classes (as the last
    resort before failing) *)
val inh_app_fun : program_mode:bool -> resolve_tc:bool -> ?use_coercions:bool ->
  env -> evar_map -> ?flags:Evarconv.unify_flags -> delayed_app_body -> types -> evar_map * delayed_app_body * types * coercion_trace
