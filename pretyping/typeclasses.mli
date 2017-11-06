(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Evd
open Environ

type direction = Forward | Backward

(** This module defines type-classes *)
type typeclass = {
  (** The toplevel universe quantification in which the typeclass lives. In
      particular, [cl_props] and [cl_context] are quantified over it. *)
  cl_univs : Univ.AUContext.t;

  (** The class implementation: a record parameterized by the context with defs in it or a definition if
     the class is a singleton. This acts as the class' global identifier. *)
  cl_impl : global_reference;

  (** Context in which the definitions are typed. Includes both typeclass parameters and superclasses.
      The global reference gives a direct link to the class itself. *)
  cl_context : global_reference option list * Context.Rel.t;

  (** Context of definitions and properties on defs, will not be shared *)
  cl_props : Context.Rel.t;

  (** The methods implementations of the typeclass as projections. 
      Some may be undefinable due to sorting restrictions or simply undefined if 
      no name is provided. The [int option option] indicates subclasses whose hint has
      the given priority. *)
  cl_projs : (Name.t * (direction * Vernacexpr.hint_info_expr) option * Constant.t option) list;

  (** Whether we use matching or full unification during resolution *)
  cl_strict : bool; 

  (** Whether we can assume that instances are unique, which allows 
      no backtracking and sharing of resolution. *)
  cl_unique : bool; 
}

type instance

val instances : global_reference -> instance list
val typeclasses : unit -> typeclass list
val all_instances : unit -> instance list

val add_class : typeclass -> unit

val new_instance : typeclass -> Vernacexpr.hint_info_expr -> bool ->
  global_reference -> instance
val add_instance : instance -> unit
val remove_instance : instance -> unit

val class_info : global_reference -> typeclass (** raises a UserError if not a class *)


(** These raise a UserError if not a class.
    Caution: the typeclass structures is not instantiated w.r.t. the universe instance.
    This is done separately by typeclass_univ_instance. *)
val dest_class_app : env -> evar_map -> EConstr.constr -> (typeclass * EConstr.EInstance.t) * constr list

(** Get the instantiated typeclass structure for a given universe instance. *)
val typeclass_univ_instance : typeclass Univ.puniverses -> typeclass

(** Just return None if not a class *)
val class_of_constr : evar_map -> EConstr.constr -> (EConstr.rel_context * ((typeclass * EConstr.EInstance.t) * constr list)) option
  
val instance_impl : instance -> global_reference

val hint_priority : instance -> int option

val is_class : global_reference -> bool
val is_instance : global_reference -> bool

(** Returns the term and type for the given instance of the parameters and fields
   of the type class. *)

val instance_constructor : typeclass EConstr.puniverses -> EConstr.t list ->
  EConstr.t option * EConstr.t

(** Filter which evars to consider for resolution. *)
type evar_filter = Evar.t -> Evar_kinds.t -> bool
val all_evars : evar_filter
val all_goals : evar_filter
val no_goals : evar_filter
val no_goals_or_obligations : evar_filter

(** Resolvability.
    Only undefined evars can be marked or checked for resolvability. *)

val set_resolvable : Evd.Store.t -> bool -> Evd.Store.t
val is_resolvable : evar_info -> bool
val mark_unresolvable : evar_info -> evar_info
val mark_unresolvables : ?filter:evar_filter -> evar_map -> evar_map
val mark_resolvables   : ?filter:evar_filter -> evar_map -> evar_map
val mark_resolvable : evar_info -> evar_info
val is_class_evar : evar_map -> evar_info -> bool
val is_class_type : evar_map -> EConstr.types -> bool

val resolve_typeclasses : ?fast_path:bool -> ?filter:evar_filter -> ?unique:bool ->
  ?split:bool -> ?fail:bool -> env -> evar_map -> evar_map
val resolve_one_typeclass : ?unique:bool -> env -> evar_map -> EConstr.types -> evar_map * EConstr.constr

val set_typeclass_transparency_hook : (evaluable_global_reference -> bool (*local?*) -> bool -> unit) Hook.t
val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

val classes_transparent_state_hook : (unit -> transparent_state) Hook.t
val classes_transparent_state : unit -> transparent_state

val add_instance_hint_hook : 
  (Globnames.global_reference_or_constr -> global_reference list ->
   bool (* local? *) -> Vernacexpr.hint_info_expr -> Decl_kinds.polymorphic -> unit) Hook.t
val remove_instance_hint_hook : (global_reference -> unit) Hook.t
val add_instance_hint : Globnames.global_reference_or_constr -> global_reference list ->
  bool -> Vernacexpr.hint_info_expr -> Decl_kinds.polymorphic -> unit
val remove_instance_hint : global_reference -> unit

val solve_all_instances_hook : (env -> evar_map -> evar_filter -> bool -> bool -> bool -> evar_map) Hook.t
val solve_one_instance_hook : (env -> evar_map -> EConstr.types -> bool -> evar_map * EConstr.constr) Hook.t

val declare_instance : Vernacexpr.hint_info_expr option -> bool -> global_reference -> unit


(** Build the subinstances hints for a given typeclass object.
    check tells if we should check for existence of the 
    subinstances and add only the missing ones. *)

val build_subclasses : check:bool -> env -> evar_map -> global_reference ->
		       Vernacexpr.hint_info_expr ->
		       (global_reference list * Vernacexpr.hint_info_expr * constr) list
