(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Vernacexpr
open Constrexpr
open Impargs
open Globnames

val primitive_flag : bool ref

(** [declare_projections ref name coers params fields] declare projections of
   record [ref] (if allowed) using the given [name] as argument, and put them
   as coercions accordingly to [coers]; it returns the absolute names of projections *)

val declare_projections :
  inductive -> ?kind:Decl_kinds.definition_object_kind -> Id.t ->
  coercion_flag list -> manual_explicitation list list -> Context.Rel.t ->
  (Name.t * bool) list * constant option list

val declare_structure :
  Decl_kinds.recursivity_kind ->
  bool (** polymorphic?*) ->
  (Univ.universe_context * Univ.universe_context) (** universe and subtyping constraints *) ->
  Id.t -> Id.t ->
  manual_explicitation list -> Context.Rel.t -> (** params *) constr -> (** arity *)
  bool (** template arity ? *) ->
  Impargs.manual_explicitation list list -> Context.Rel.t -> (** fields *)
  ?kind:Decl_kinds.definition_object_kind -> ?name:Id.t ->
  bool -> (** coercion? *)
  bool list -> (** field coercions *)
  Evd.evar_map ->
  inductive

val definition_structure :
  inductive_kind * Decl_kinds.polymorphic * Decl_kinds.recursivity_kind *
  plident with_coercion * local_binder_expr list *
  (local_decl_expr with_instance with_priority with_notation) list *
  Id.t * constr_expr option -> global_reference

val declare_existing_class : global_reference -> unit
