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
open Entries
open Decl_kinds

(** This module provides the official functions to declare new variables,
   parameters, constants and inductive types. Using the following functions
   will add the entries in the global environment (module [Global]), will
   register the declarations in the library (module [Lib]) --- so that the
   reset works properly --- and will fill some global tables such as
   [Nametab] and [Impargs]. *)

(** Declaration of local constructions (Variable/Hypothesis/Local) *)

type section_variable_entry =
  | SectionLocalDef of Evd.side_effects Proof_global.proof_entry
  | SectionLocalAssum of { typ:types; univs:Univ.ContextSet.t; poly:bool; impl:bool }

type 'a constant_entry =
  | DefinitionEntry of 'a Proof_global.proof_entry
  | ParameterEntry of parameter_entry
  | PrimitiveEntry of primitive_entry

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

val declare_variable : variable -> variable_declaration -> Libobject.object_name

(** Declaration of global constructions
   i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = Evd.side_effects constant_entry * logical_kind

(* Default definition entries, transparent with no secctx or proj information *)
val definition_entry : ?fix_exn:Future.fix_exn ->
  ?opaque:bool -> ?inline:bool -> ?types:types ->
  ?univs:Entries.universes_entry ->
  ?eff:Evd.side_effects -> constr -> Evd.side_effects Proof_global.proof_entry

type import_status = ImportDefaultBehavior | ImportNeedQualified

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  internal specify if the constant has been created by the kernel or by the
  user, and in the former case, if its errors should be silent *)
val declare_constant :
 ?local:import_status -> Id.t -> constant_declaration -> Constant.t

val declare_private_constant :
  ?role:Evd.side_effect_role -> ?local:import_status -> Id.t -> constant_declaration -> Constant.t * Evd.side_effects

val declare_definition :
  ?opaque:bool -> ?kind:definition_object_kind ->
  ?local:import_status -> Id.t -> ?types:constr ->
  constr Entries.in_universes_entry -> Constant.t

(** Since transparent constants' side effects are globally declared, we
 *  need that *)
val set_declare_scheme :
  (string -> (inductive * Constant.t) array -> unit) -> unit

(** [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block and a boolean indicating if it is a primitive record. *)
val declare_mind : mutual_inductive_entry -> Libobject.object_name * bool

(** Declaration messages *)

val definition_message : Id.t -> unit
val assumption_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit
val cofixpoint_message : Id.t list -> unit
val recursive_message : bool (** true = fixpoint *) ->
  int array option -> Id.t list -> unit

val exists_name : Id.t -> bool

(** Global universe contexts, names and constraints *)
val declare_univ_binders : GlobRef.t -> UnivNames.universe_binders -> unit

val declare_universe_context : poly:bool -> Univ.ContextSet.t -> unit

val do_universe : poly:bool -> lident list -> unit
val do_constraint : poly:bool -> Glob_term.glob_constraint list -> unit
