(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Evd
open Environ

(* Core typeclasses hints *)
type 'a hint_info_gen =
    { hint_priority : int option;
      hint_pattern : 'a option }

type hint_info = (Id.Set.t * Pattern.constr_pattern) hint_info_gen

type class_method = {
  meth_name : Name.t;
  meth_const : Constant.t option;
}

(** This module defines type-classes *)
type typeclass = {
  cl_univs : UVars.AbstractContext.t;
  (** The toplevel universe quantification in which the typeclass lives. In
      particular, [cl_props] and [cl_context] are quantified over it. *)

  cl_impl : GlobRef.t;
  (** The class implementation: a record parameterized by the context with defs in it or a definition if
     the class is a singleton. This acts as the class' global identifier. *)

  cl_context : Constr.rel_context;
  (** Context in which the definitions are typed. *)

  cl_trivial : bool;
  (** Class declared with "Class Foo params := {}", produces 0 goals in interactive mode. *)

  cl_props : Constr.rel_context;
  (** Context of definitions and properties on defs, used for "Instance := {}".
      If [cl_impl] is a record this is the arguments of its constructor (without parameters).
      Otherwise it is a single [LocalAssum] of type convertible to [cl_impl]. *)

  cl_projs : class_method list;
  (** The methods implementations of the typeclass as projections.
      Some may be undefinable due to sorting restrictions or simply undefined if
      no name is provided. Used for dumpglob in "Instance := {}" and in elpi. *)

  cl_strict : bool;
  (** Whether we use matching or full unification during resolution *)

  cl_unique : bool;
  (** Whether we can assume that instances are unique, which allows
      no backtracking and sharing of resolution. *)
}

type instance = {
  is_class: GlobRef.t;
  is_info: hint_info;
  is_impl: GlobRef.t;
}

val instances : GlobRef.t -> instance list option
(** [None] if not a class *)

val instances_exn : env -> evar_map -> GlobRef.t -> instance list
(** raise [TypeClassError] if not a class *)

val typeclasses : unit -> typeclass list
val all_instances : unit -> instance list

val load_class : typeclass -> unit

val load_instance : instance -> unit
val remove_instance : instance -> unit

val class_info : GlobRef.t -> typeclass option
(** [None] if not a class *)

val class_info_exn : env -> evar_map -> GlobRef.t -> typeclass
(** raise [TypeClassError] if not a class *)

(** These raise a UserError if not a class.
    Caution: the typeclass structures is not instantiated w.r.t. the universe instance.
    This is done separately by typeclass_univ_instance. *)
val dest_class_app : env -> evar_map -> EConstr.constr -> (typeclass * EConstr.EInstance.t) * constr list

(** Just return None if not a class *)
val class_of_constr : env -> evar_map -> EConstr.constr ->
  (EConstr.rel_context * ((typeclass * EConstr.EInstance.t) * constr list)) option

val instance_impl : instance -> GlobRef.t

val hint_priority : instance -> int option

val is_class : GlobRef.t -> bool

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

val is_class_evar : evar_map -> undefined evar_info -> bool
val is_class_type : evar_map -> EConstr.types -> bool

val resolve_typeclasses : ?filter:evar_filter -> ?unique:bool ->
  ?fail:bool -> env -> evar_map -> evar_map

val get_filtered_typeclass_evars : evar_filter -> evar_map -> Evar.Set.t

val error_unresolvable : env -> evar_map -> Evar.Set.t -> 'a

(** A plugin can override the TC resolution engine by calling these two APIs.
    Beware this action is not registed in the summary (the Undo system) so
    it is up to the plugin to do so. *)
val set_solve_all_instances : (env -> evar_map -> evar_filter -> bool -> bool -> evar_map) -> unit

val get_typeclasses_unique_solutions : unit -> bool

(* Deprecated *)
val resolve_one_typeclass : ?unique:bool -> env -> evar_map -> EConstr.types -> evar_map * EConstr.constr
[@@deprecated "(9.0) Use Class_tactics.resolve_one_typeclass (\"unique\" argument was ignored)"]

val set_solve_one_instance : (env -> evar_map -> EConstr.types -> evar_map * EConstr.constr) -> unit
[@@deprecated "(9.0) For internal use only"]
