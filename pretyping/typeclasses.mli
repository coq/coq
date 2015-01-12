(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames
open Term
open Context
open Evd
open Environ

type direction = Forward | Backward

(** This module defines type-classes *)
type typeclass = {
  (** The class implementation: a record parameterized by the context with defs in it or a definition if
     the class is a singleton. This acts as the class' global identifier. *)
  cl_impl : global_reference;

  (** Context in which the definitions are typed. Includes both typeclass parameters and superclasses.
     The boolean indicates if the typeclass argument is a direct superclass and the global reference
     gives a direct link to the class itself. *)
  cl_context : (global_reference * bool) option list * rel_context;

  (** Context of definitions and properties on defs, will not be shared *)
  cl_props : rel_context;

  (** The methods implementations of the typeclass as projections. 
      Some may be undefinable due to sorting restrictions or simply undefined if 
      no name is provided. The [int option option] indicates subclasses whose hint has
      the given priority. *)
  cl_projs : (Name.t * (direction * int option) option * constant option) list;

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

val new_instance : typeclass -> int option -> bool -> Decl_kinds.polymorphic -> 
  global_reference -> instance
val add_instance : instance -> unit
val remove_instance : instance -> unit

val class_info : global_reference -> typeclass (** raises a UserError if not a class *)


(** These raise a UserError if not a class.
    Caution: the typeclass structures is not instantiated w.r.t. the universe instance.
    This is done separately by typeclass_univ_instance. *)
val dest_class_app : env -> constr -> typeclass puniverses * constr list

(** Get the instantiated typeclass structure for a given universe instance. *)
val typeclass_univ_instance : typeclass puniverses -> typeclass puniverses

(** Just return None if not a class *)
val class_of_constr : constr -> (rel_context * (typeclass puniverses * constr list)) option
  
val instance_impl : instance -> global_reference

val instance_priority : instance -> int option

val is_class : global_reference -> bool
val is_instance : global_reference -> bool

val is_implicit_arg : Evar_kinds.t -> bool

(** Returns the term and type for the given instance of the parameters and fields
   of the type class. *)

val instance_constructor : typeclass puniverses -> constr list -> 
  constr option * types

(** Filter which evars to consider for resolution. *)
type evar_filter = existential_key -> Evar_kinds.t -> bool
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
val is_class_type : evar_map -> types -> bool

val resolve_typeclasses : ?filter:evar_filter -> ?unique:bool -> 
  ?split:bool -> ?fail:bool -> env -> evar_map -> evar_map
val resolve_one_typeclass : ?unique:bool -> env -> evar_map -> types -> open_constr

val set_typeclass_transparency_hook : (evaluable_global_reference -> bool (*local?*) -> bool -> unit) Hook.t
val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

val classes_transparent_state_hook : (unit -> transparent_state) Hook.t
val classes_transparent_state : unit -> transparent_state

val add_instance_hint_hook : 
  (global_reference_or_constr -> global_reference list ->
   bool (* local? *) -> int option -> Decl_kinds.polymorphic -> unit) Hook.t
val remove_instance_hint_hook : (global_reference -> unit) Hook.t
val add_instance_hint : global_reference_or_constr -> global_reference list -> 
  bool -> int option -> Decl_kinds.polymorphic -> unit
val remove_instance_hint : global_reference -> unit

val solve_instantiations_problem : (env -> evar_map -> evar_filter -> bool -> bool -> bool -> evar_map) ref
val solve_instantiation_problem : (env -> evar_map -> types -> bool -> open_constr) ref

val declare_instance : int option -> bool -> global_reference -> unit


(** Build the subinstances hints for a given typeclass object.
    check tells if we should check for existence of the 
    subinstances and add only the missing ones. *)

val build_subclasses : check:bool -> env -> evar_map -> global_reference -> int option (* priority *) ->
  (global_reference list * int option * constr) list
