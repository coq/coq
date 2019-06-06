(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Evd
open Environ

type direction = Forward | Backward

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Pattern.patvar list * Pattern.constr_pattern) hint_info_gen

(** This module defines type-classes *)
type typeclass = {
  cl_univs : Univ.AUContext.t;
  (** The toplevel universe quantification in which the typeclass lives. In
      particular, [cl_props] and [cl_context] are quantified over it. *)

  cl_impl : GlobRef.t;
  (** The class implementation: a record parameterized by the context with defs in it or a definition if
     the class is a singleton. This acts as the class' global identifier. *)

  cl_context : GlobRef.t option list * Constr.rel_context;
  (** Context in which the definitions are typed. Includes both typeclass parameters and superclasses.
      The global reference gives a direct link to the class itself. *)

  cl_props : Constr.rel_context;
  (** Context of definitions and properties on defs, will not be shared *)

  cl_projs : (Name.t * (direction * hint_info) option * Constant.t option) list;
  (** The methods implementations of the typeclass as projections. 
      Some may be undefinable due to sorting restrictions or simply undefined if 
      no name is provided. The [int option option] indicates subclasses whose hint has
      the given priority. *)

  cl_strict : bool; 
  (** Whether we use matching or full unification during resolution *)

  cl_unique : bool;
  (** Whether we can assume that instances are unique, which allows 
      no backtracking and sharing of resolution. *)
}

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  (* Sections where the instance should be redeclared,
     None for discard, Some 0 for none. *)
  is_global: int option;
  is_impl: GlobRef.t;
}

val instances : env -> evar_map -> GlobRef.t -> instance list
val typeclasses : unit -> typeclass list
val all_instances : unit -> instance list

val load_class : typeclass -> unit

val load_instance : instance -> unit
val remove_instance : instance -> unit

val class_info : env -> evar_map -> GlobRef.t -> typeclass (** raises a UserError if not a class *)


(** These raise a UserError if not a class.
    Caution: the typeclass structures is not instantiated w.r.t. the universe instance.
    This is done separately by typeclass_univ_instance. *)
val dest_class_app : env -> evar_map -> EConstr.constr -> (typeclass * EConstr.EInstance.t) * constr list

(** Get the instantiated typeclass structure for a given universe instance. *)
val typeclass_univ_instance : typeclass Univ.puniverses -> typeclass

(** Just return None if not a class *)
val class_of_constr : env -> evar_map -> EConstr.constr ->
  (EConstr.rel_context * ((typeclass * EConstr.EInstance.t) * constr list)) option

val instance_impl : instance -> GlobRef.t

val hint_priority : instance -> int option

val is_class : GlobRef.t -> bool

(** Returns the term and type for the given instance of the parameters and fields
   of the type class. *)

val instance_constructor : typeclass EConstr.puniverses -> EConstr.t list ->
  EConstr.t option * EConstr.t

(** Filter which evars to consider for resolution. *)
type evar_filter = Evar.t -> Evar_kinds.t Lazy.t -> bool
val all_evars : evar_filter
val all_goals : evar_filter
val no_goals : evar_filter
val no_goals_or_obligations : evar_filter

(** Resolvability.
    Only undefined evars can be marked or checked for resolvability.
    They represent type-class search roots.

    A resolvable evar is an evar the type-class engine may try to solve
    An unresolvable evar is an evar the type-class engine will NOT try to solve
*)

val make_unresolvables : (Evar.t -> bool) -> evar_map -> evar_map

val is_class_evar : evar_map -> evar_info -> bool
val is_class_type : evar_map -> EConstr.types -> bool

val resolve_typeclasses : ?filter:evar_filter -> ?unique:bool ->
  ?split:bool -> ?fail:bool -> env -> evar_map -> evar_map
val resolve_one_typeclass : ?unique:bool -> env -> evar_map -> EConstr.types -> evar_map * EConstr.constr

val set_typeclass_transparency_hook : (evaluable_global_reference -> bool (*local?*) -> bool -> unit) Hook.t
val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

val classes_transparent_state_hook : (unit -> TransparentState.t) Hook.t
val classes_transparent_state : unit -> TransparentState.t

val solve_all_instances_hook : (env -> evar_map -> evar_filter -> bool -> bool -> bool -> evar_map) Hook.t
val solve_one_instance_hook : (env -> evar_map -> EConstr.types -> bool -> evar_map * EConstr.constr) Hook.t

(** Build the subinstances hints for a given typeclass object.
    check tells if we should check for existence of the 
    subinstances and add only the missing ones. *)

val build_subclasses : check:bool -> env -> evar_map -> GlobRef.t ->
                       hint_info ->
                       (GlobRef.t list * hint_info * constr) list
