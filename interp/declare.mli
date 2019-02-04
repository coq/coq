(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
  | SectionLocalDef of Safe_typing.private_constants definition_entry
  | SectionLocalAssum of types Univ.in_universe_context_set * polymorphic * bool (** Implicit status *)

type variable_declaration = DirPath.t * section_variable_entry * logical_kind

val declare_variable : variable -> variable_declaration -> Libobject.object_name

(** Declaration of global constructions 
   i.e. Definition/Theorem/Axiom/Parameter/... *)

type constant_declaration = Safe_typing.private_constants constant_entry * logical_kind

type internal_flag =
  | UserAutomaticRequest
  | InternalTacticRequest
  | UserIndividualRequest

(* Defaut definition entries, transparent with no secctx or proj information *)
val definition_entry : ?fix_exn:Future.fix_exn ->
  ?opaque:bool -> ?inline:bool -> ?types:types ->
  ?univs:Entries.constant_universes_entry ->
  ?eff:Safe_typing.private_constants -> constr -> Safe_typing.private_constants definition_entry

(** [declare_constant id cd] declares a global declaration
   (constant/parameter) with name [id] in the current section; it returns
   the full path of the declaration

  internal specify if the constant has been created by the kernel or by the
  user, and in the former case, if its errors should be silent *)
val declare_constant :
 ?internal:internal_flag -> ?local:bool -> Id.t -> ?export_seff:bool -> constant_declaration -> Constant.t

val declare_definition : 
  ?internal:internal_flag -> ?opaque:bool -> ?kind:definition_object_kind ->
  ?local:bool -> Id.t -> ?types:constr ->
  constr Entries.in_constant_universes_entry -> Constant.t

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
val register_message : Id.t -> unit
val fixpoint_message : int array option -> Id.t list -> unit
val cofixpoint_message : Id.t list -> unit
val recursive_message : bool (** true = fixpoint *) ->
  int array option -> Id.t list -> unit

val exists_name : Id.t -> bool

(** Global universe contexts, names and constraints *)
val declare_univ_binders : GlobRef.t -> UnivNames.universe_binders -> unit

val declare_universe_context : polymorphic -> Univ.ContextSet.t -> unit

val do_universe : polymorphic -> lident list -> unit
val do_constraint : polymorphic -> (Glob_term.glob_level * Univ.constraint_type * Glob_term.glob_level) list ->
                    unit
