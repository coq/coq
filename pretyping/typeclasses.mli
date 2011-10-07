(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util

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
      no name is provided. The boolean indicates subclasses. *)
  cl_projs : (name * bool * constant option) list;
}

type instance

val instances : global_reference -> instance list
val typeclasses : unit -> typeclass list
val all_instances : unit -> instance list

val add_class : typeclass -> unit

val add_constant_class : constant -> unit

val add_inductive_class : inductive -> unit

val new_instance : typeclass -> int option -> bool -> global_reference -> instance
val add_instance : instance -> unit
val remove_instance : instance -> unit

val class_info : global_reference -> typeclass (** raises a UserError if not a class *)


(** These raise a UserError if not a class. *)
val dest_class_app : env -> constr -> typeclass * constr list

(** Just return None if not a class *)
val class_of_constr : constr -> (rel_context * (typeclass * constr list)) option
  
val instance_impl : instance -> global_reference

val is_class : global_reference -> bool
val is_instance : global_reference -> bool

val is_implicit_arg : hole_kind -> bool

(** Returns the term and type for the given instance of the parameters and fields
   of the type class. *)

val instance_constructor : typeclass -> constr list -> constr option * types

(** Resolvability.
    Only undefined evars could be marked or checked for resolvability. *)

val is_resolvable : evar_info -> bool
val mark_unresolvable : evar_info -> evar_info
val mark_unresolvables : evar_map -> evar_map
val is_class_evar : evar_map -> evar_info -> bool

val resolve_typeclasses : ?onlyargs:bool -> ?split:bool -> ?fail:bool ->
  env -> evar_map -> evar_map
val resolve_one_typeclass : env -> evar_map -> types -> open_constr

val register_set_typeclass_transparency : (evaluable_global_reference -> bool (*local?*) -> bool -> unit) -> unit
val set_typeclass_transparency : evaluable_global_reference -> bool -> bool -> unit

val register_classes_transparent_state : (unit -> transparent_state) -> unit
val classes_transparent_state : unit -> transparent_state

val register_add_instance_hint : (global_reference -> bool (* local? *) -> int option -> unit) -> unit
val register_remove_instance_hint : (global_reference -> unit) -> unit
val add_instance_hint : global_reference -> bool -> int option -> unit
val remove_instance_hint : global_reference -> unit

val solve_instanciations_problem : (env -> evar_map -> bool -> bool -> bool -> evar_map) ref
val solve_instanciation_problem : (env -> evar_map -> types -> open_constr) ref
